/*

  ROOT macro that will take the ASCII formatted output files of SIMION, a GEANT4 simulation, and Master event file and output a ROOT file containing one TTree object filled with simulation data...

  For the moment the information file will be read into a third branch

  TTree
  |---> Branch (MASTER DECAY DATA)
  |---> Branch (SIMION DATA)
  |---> Branch (GEANT4 DATA)

  bdnknit_v0.1aa.cc: ROOT macro version of bdnknit_v0.1a.cxx; suitable for sorting the early 134Sb ground state decays (doesn't support conversion electron emission...)

  bdnknit_v0.2a.cc: ROOT macro version of bdnknit w/ handling for multiple gammas and conversion electrons.  Version v0.2a -> Just MASTER File events (new format...)

  bdnknit_v0.2b.cc: MASTER + SIMION data...

  bdnknit_v0.2c.cc: First version to work for all data.  Works for test 134Sb_gs simulation data.

  bdnknit_v0.2d.cc: first "viable" version for new data stream (works on other platforms)

  bdnknit_v0.2e.cc: Added kOverwrite flag to bdntree->Write("",TObject::kOverwrite) to see if namecycle issue is related to missing events.

  bdnknit_v0.2f.cc: Changed conditional statement for bdntree->Write() call; geant event number must be >= master event number.

  bdnknit_v0.2g.cc: Expanding GEANT4_OUT struct to include arrays for particle data, just as in the MASTER struct.  Thus, only one instand of each struct will is necessary for each decay (and also each TTree entry).  Note this version only worked for "gamma" output from the beta decay code.

  bdnknit_v0.2h.cc: Added "sum_" variables to GEANT4_OUT struct for each plastic detector.  Should be able to generate total detected energy spectra.  
                    Added proper handling for neutron data in tree and as GEANT4 particles.  Neutrons have a pid=3
		    Added statistics on detected singles and coincidences.  Note: this doesn't represent which detector(s) the particles were detected in, 
		    only that they deposited energy in at least one.
*/
#include "stdio.h"
#include "string.h"
#include "TFile.h"
#include "TMath.h"
#include "TROOT.h"
#include "TTree.h"
#include "TBranch.h"
using namespace std;


const int MAXLEN=300;
const int NSI=13;//number of datawords to read from SIMION output
const int NG4=7;//number of datawords to read from GEANT4 output
const int MAXG=10; //max number of gammas in cascade
const int MAXCE=5; //max number of conversion electrons in decay
const int MAXN=1; //max number of neutrons in decay

typedef struct{
  int evtnum;
  int evttype;
  float tof;
  float mass;
  int q;
  float pos_x;
  float pos_y;
  float pos_z;
  float vel;
  float phi;
  float theta;
  float ke;
  float ke_err;
} SIMION_OUT;

typedef struct{
  int evtnum;
  int pid[MAXG+MAXCE+1]; //0 for beta, 1 for gamma, 2 for conversion electron, 3 for neutron
  float mcp_t[MAXG+MAXCE+1];
  //  float sum_t_mcp;
  float mcp_r[MAXG+MAXCE+1];
  //float sum_r_mcp;
  float de_l[MAXG+MAXCE+1];
  float sum_de_l;
  float e_l[MAXG+MAXCE+1];
  float sum_e_l;
  float de_b[MAXG+MAXCE+1];
  float sum_de_b;
  float e_b[MAXG+MAXCE+1];
  float sum_e_b;
} GEANT4_OUT;

typedef struct{
  int evtnum;
  float tob;
  int num_state;
  float e_state;
  int q_state;
  float decay_x, decay_y, decay_z;
  float nu_E, nu_px, nu_py, nu_pz;
  float beta_E, beta_px, beta_py, beta_pz;
  float rec_E, rec_px, rec_py, rec_pz;
  int gammanum;
  float g_E[MAXG], g_px[MAXG], g_py[MAXG], g_pz[MAXG];
  int cenum;
  float ce_E[MAXCE], ce_px[MAXCE], ce_py[MAXCE], ce_pz[MAXCE];
  int nnum;
  float n_E[MAXN], n_px[MAXN], n_py[MAXN], n_pz[MAXN];
} MASTER_EVT;

static SIMION_OUT s;
static GEANT4_OUT g;
static MASTER_EVT m;

//int main(int argc, char * argv[]){
int bdnknit(const char *fnMASTER,const char* fnGEANT, const char *fnSIMION, const char *fnROOT, int nevent=-1, int iverb=0){

  FILE *fSIMION,*fGEANT,*fMASTER;
  TFile *fROOT;
  TTree *bdntree;
  char *cS, *cG, *cM, str0[MAXLEN],str1[MAXLEN],str2[MAXLEN];
  int lines[3]={0,0,0},n[3]={0,0,0},isgood[3], isok=0, NGP=0, j=0;
  int nbeta[MAXG][MAXCE], det[4]={0,0,0,0},det_b=0, det_g=0, det_ce=0, det_n=0, det_bg=0, det_bce=0, det_bn=0, det_bgce=0;

  //zero out nbeta array
  for(int a=0;a<MAXG;++a){
    for(int b=0;b<MAXCE;++b){
      nbeta[a][b]=0;
    }
  }

  //OBSOLETE  const char *s_msg="Syntax: bdnknit -n [# events] [MASTER Decay File] [GEANT4 output] [SIMION output] [ROOT Filename]";
  //OBSOLETE int nmarg=1,nsarg=2,ngarg=3,noarg=4; //set default command line indicies

  int N=0,nloops=0, maxloops=100000000;  //nloops set to large default value... program should exit on EOF

  if(nevent>0) maxloops=nevent;

  fMASTER=fopen(fnMASTER,"r"); //open MASTER Output for reading
  if(!fMASTER) {fprintf(stderr,"Error opening file \"%s\"\n",fnMASTER); return -1;}

  fGEANT=fopen(fnGEANT,"r"); //open GEANT4 Output for reading
  if(!fGEANT) {fprintf(stderr,"Error opening file \"%s\"\n",fnGEANT); return -2;}

  fSIMION=fopen(fnSIMION,"r"); //open SIMION Output for reading
  if(!fSIMION) {fprintf(stderr,"Error opening file \"%s\"\n",fnSIMION); return -3;}

  fROOT=new TFile(fnROOT, "recreate"); //(re)create ROOT file
  if(fROOT->IsZombie()) {fprintf(stderr,"Error creating ROOT file \"%s\"\n",fnROOT); return -4;}


  //create TTree
  bdntree=new TTree("bdntree","BDN Simulation data");
  bdntree->Branch("master",&m,"evtnum/I:tob/F:num_state/I:e_state/F:q_state/I:decay_x/F:decay_y:decay_z:nu_E:nu_px:nu_py:nu_pz:beta_E:beta_px:beta_py:beta_pz:rec_E:rec_px:rec_py:rec_pz:gammanum/I:g_E[10]/F:g_px[10]:g_py[10]:g_pz[10]:cenum/I:ce_E[5]/F:ce_px[5]:ce_py[5]:ce_pz[5]:nnum/I:n_E[1]/F:n_px[1]:n_py[1]:n_pz[1]");
  bdntree->Branch("geant",&g,"evtnum/I:pid[16]:mcp_t[16]/F:mcp_r[16]:de_l[16]:sum_de_l:e_l[16]:sum_e_l:de_b[16]:sum_de_b:e_b[16]:sum_e_b");
  bdntree->Branch("simion",&s,"evtnum/I:evttype:tof/F:mass:q/I:pos_x/F:pos_y:pos_z:vel:phi:theta:ke:ke_err");
 
  //read in first line of all files (mostly headers...)
  for(int i=0;i<11;++i) cM=fgets(str0,MAXLEN,fMASTER);  //ignore header in MASTER/AUX file
  
  cG=fgets(str1,MAXLEN,fGEANT);
  cS=fgets(str2,MAXLEN,fSIMION);
  
  /************!!!!!BEGIN LOOPING OVER INPUT FILES!!!!!*************/

  while(cS!=NULL&&cG!=NULL&&cM!=NULL&&!feof(fSIMION)&&!feof(fGEANT)&&!feof(fMASTER)&&nloops<maxloops){
    j=0;
    isgood[0]=isgood[1]=isgood[2]=0;
    det[0]=det[1]=det[2]=det[3]=0;
    g.sum_de_l=g.sum_e_l=g.sum_de_b=g.sum_e_b=0;

    /*********************************************************************/
    /****************************MASTER FILE******************************/
    /*********************************************************************/
    //need to find the position of all commas in the line taken from the MASTER file (because CINT will only allow 12 sscanf args per call...dumb)
            
    const char *p2=0;
    int ind2=0, d2[80];

    //zero out d2 array....you should rename the array...
    for(int i=0;i<80;++i) d2[i]=0;

    //read in master decay file...
    do{
 
      if(iverb) fprintf(stderr,"%s",str0);
      n[0]=sscanf(str0,"%i, %f, %i, %f, %i, %f, %f, %f",&m.evtnum,&m.tob,&m.num_state,&m.e_state,&m.q_state,&m.decay_x,&m.decay_y,&m.decay_z);
      if(iverb) fprintf(stderr,"m0:%i %s\n",n[0],str0);
      cM=fgets(str0,MAXLEN,fMASTER);
      n[0]+=sscanf(str0,"%f, %f, %f, %f",&m.nu_E,&m.nu_px,&m.nu_py,&m.nu_pz);
      if(iverb) fprintf(stderr,"m1:%i %s\n",n[0],str0);
      cM=fgets(str0,MAXLEN,fMASTER);
      n[0]+=sscanf(str0,"%f, %f, %f, %f",&m.beta_E,&m.beta_px,&m.beta_py,&m.beta_pz);
      if(iverb) fprintf(stderr,"m2:%i %s\n",n[0],str0);
      cM=fgets(str0,MAXLEN,fMASTER);
      n[0]+=sscanf(str0,"%f, %f, %f, %f",&m.rec_E,&m.rec_px,&m.rec_py,&m.rec_pz);
      if(iverb) fprintf(stderr,"m3:%i %s\n",n[0],str0);
      cM=fgets(str0,MAXLEN,fMASTER);
      n[0]+=sscanf(str0,"%i",&m.gammanum);
      if(iverb) fprintf(stderr,"m.gammanum:%i %s\n",n[0],str0); 

      for(int i=0;i<m.gammanum;++i){
	cM=fgets(str0,MAXLEN,fMASTER);
	n[0]+=sscanf(str0,"%f, %f, %f, %f",&m.g_E[i],&m.g_px[i],&m.g_py[i],&m.g_pz[i]);
	if(iverb) fprintf(stderr,"m%i:%i %s\n",i+4,n[0],str0);
      }
     
      cM=fgets(str0,MAXLEN,fMASTER);
      n[0]+=sscanf(str0,"%i",&m.cenum);
      if(iverb) fprintf(stderr,"m.cenum:%i %s\n",n[0],str0);

      for(int i=0;i<m.cenum;++i){
	cM=fgets(str0,MAXLEN,fMASTER);
	n[0]+=sscanf(str0,"%f, %f, %f, %f",&m.ce_E[i],&m.ce_px[i],&m.ce_py[i],&m.ce_pz[i]);
	if(iverb) fprintf(stderr,"m%i:%i %s\n",i+5+m.gammanum,n[0],str0);
      }    
      
      cM=fgets(str0,MAXLEN,fMASTER);
      n[0]+=sscanf(str0,"%i",&m.nnum);
      if(iverb) fprintf(stderr,"m.nnum:%i %s\n",n[0],str0);
      if(m.nnum>0) cM=fgets(str0,MAXLEN,fMASTER);
      // if(m.nnum<=MAXN){
      if(m.nnum==0){
	m.n_E[0]=0;
	m.n_px[0]=0;
	m.n_py[0]=0;
	m.n_pz[0]=0;
      }
      if(m.nnum==1){       	
       	n[0]+=sscanf(str0,"%f, %f, %f, %f",&m.n_E[0],&m.n_px[0],&m.n_py[0],&m.n_pz[0]);
	if(iverb) {fprintf(stderr,"neutron: %f %f %f %f\n",m.n_E[0],m.n_px[0],m.n_py[0],m.n_pz[0]);}
	//if(iverb) {fprintf(stderr,"m%i:%i %s\n",m.gammanum+m.cenum+6,n[0],str0);}
	
      }
      
      //min # of words = 23, max#=20+NGMAX(=10)*4+NCEMAX(=5)*4+NNMAX(=1)*4=84
      if(n[0]>=23&&n[0]<=84){
	++lines[0];  
	isgood[0]=1; 
      }
      cM=fgets(str0,MAXLEN,fMASTER);
      //      ind0=0;
    } while(!isgood[0]&&!feof(fMASTER));
  
    //Define the number of GEANT "particles" to read...
    NGP=(m.gammanum+m.cenum+m.nnum+1); //# gammas + # conv. electrons + 1 beta
    if(iverb)fprintf(stderr,"\n!!!# GEANT particles = %i!!!\n",NGP);
    if(iverb) fprintf(stderr,"#gammas:%i #ces:%i (1 beta)\n",m.gammanum,m.cenum);

    /*********************************************************************/
    /****************************SIMION FILE******************************/
    /*********************************************************************/

    // need to find the position of all tab characters ('\t') in the line taken 
    // from the SIMION file (because CINT will only allow 12 sscanf args per call...which as mentioned before...is dumb)

    p2 = strpbrk(str2,"\t");  //locate pointer for pointer to first comma
    while(p2!=NULL){      //Now loop over every character
      d2[ind2]=p2-str2;  //assign relative index to array   
      if(iverb) fprintf(stderr,"%i:%i ",ind2,d2[ind2]);
      ++ind2;
      p2=strpbrk(p2+1,"\t");
    } 
    if(iverb) fprintf(stderr,"\n");
    //reference the tab position array (d2[]) when reading in SIMION File

    //read in line of SIMION output file
    do{
      if(iverb) fprintf(stderr,"%s",str2);
      n[2]=sscanf(str2,"%i %i %f %f %i %f %f %f",&s.evtnum,&s.evttype,&s.tof,&s.mass,&s.q,&s.pos_x,&s.pos_y,&s.pos_z);
      if(iverb) fprintf(stderr,"s:%i\n",n[2]);
      n[2]+=sscanf(&str2[d2[7]],"%f %f %f %f %f",&s.vel,&s.phi,&s.theta,&s.ke,&s.ke_err);
      if(iverb) fprintf(stderr,"s:%i\n",n[2]);
      if(n[2]==NSI){
    	++lines[2];
    	isgood[2]=1;
      }
      cS=fgets(str2,MAXLEN,fSIMION);
      ind2=0;
    } while(!isgood[2]&&!feof(fSIMION)); //loop exits when a "good" event is read or the end of file is reached
    
    /*********************************************************************/
    /*****************************GEANT FILE******************************/
    /*********************************************************************/
	
    //read in lines GEANT output file and fill tree according to number of particles
    //since # of lines to read is known (NGP) using for LCV

    // The GEANT outputs are listed in the following order (for beta-gamma simulations):
    // (Beta) eventnum, mcp_t, ...
    // (Gamma #1) eventnum, mcp_t, ...
    // (Gamma #2) eventnum, mcp_t, ...
    // ...
    // (CE #1) eventnum, mcp_t, ...
    // (CE #2) eventnum, mcp_t, ...

    // The GEANT outputs are listed in the following order (for beta-neutron simulations):
    // (Beta) eventnum, mcp_t, ...
    // (Neutron) eventnum, mcp_t, ...
    
    //loop over each GEANT particle and store it in the GEANT4_OUT struct...
    
    do{
      //isok=0;  //reset isgood flag
		
	if(iverb) fprintf(stderr,"read line:%s",str1);
	n[1]=sscanf(str1,"%i, %f, %f, %f, %f, %f, %f",&g.evtnum,&g.mcp_t[j],&g.mcp_r[j],&g.de_l[j],&g.e_l[j],&g.de_b[j],&g.e_b[j]);
	if(iverb) fprintf(stderr,"gB(%i):%i\n",j,n[1]);      
	if(n[1]==NG4){
	  //Assign particle id
	  if(j==0)g.pid[j]=0;
	  if(m.nnum>0&&j==1) g.pid[j]=3;
	  else{
	    if(j>0&&j<=m.gammanum) g.pid[j]=1;
	    if(j>m.gammanum&&j<=NGP) g.pid[j]=2;
	  }
	  if(iverb) fprintf(stderr,"GOOD GEANT DATA: m.evtnum=%i g.evtnum=%i j=%i g.pid=%i\n",m.evtnum,g.evtnum,j,g.pid[j]);      
	  ++isgood[1];
	  ++lines[1];
	  ++j;
	}
	cG=fgets(str1,MAXLEN,fGEANT);
    } while (j<NGP&&!feof(fGEANT)); //evaluate, error check, skip bad input---> exit if exceed the number of GEANT "particles" OR EOF


    for(int i=0;i<NGP;++i){
      //calculate total energies in each plastic detector
      g.sum_de_l+=g.de_l[i];
      g.sum_e_l+=g.e_l[i];
      g.sum_de_b+=g.de_b[i];
      g.sum_e_b+=g.e_b[i];

      if(g.mcp_t[i]||g.mcp_r[i]||g.de_l[i]||g.e_l[i]||g.de_b[i]||g.e_b[i]) //count detetected particles (singles)

	{
	  switch(g.pid[i]){
	  case 0: {++det_b; ++det[0]; break;}
	  case 1: {++det_g; ++det[1]; break;}
	  case 2: {++det_ce; ++det[2];break;}
	  case 3: {++det_n; ++det[3]; break;}
	  }
	}
    }
    //count detected coincidences
    if(det[0]){
      if(det[1]) {
	++det_bg;
	if(det[2]) ++det_bgce;
      }
      if(det[2]) ++det_bce;
      if(det[3]) ++det_bn;
    }


    /******INTEGRITY CHECK BEFORE FILLING TTREE******/
    //check to ensure that MASTER, SIMION, & GEANT4 data read in are "good"
    // fprintf(stderr,"isgood: %i %i %i\n",isgood[0],isgood[1],isgood[2]);

    if(isgood[0]&&(isgood[1]==NGP)&&isgood[2]){
      //check to see if event numbers are the same
      if(iverb) fprintf(stderr,"evt#: %i %i %i\n",m.evtnum,g.evtnum,s.evtnum);
      if(m.evtnum==s.evtnum) {
	++nbeta[m.gammanum][m.cenum]; //counter for beta-#gamma-#ce events
	bdntree->Fill(); //fill tree
	if(iverb) fprintf(stderr,"...filling tree!\n");
      }
      else {fprintf(stderr,"failed evtnum: %i %i %i\n",m.evtnum,g.evtnum,s.evtnum);}   
    } 
    else {fprintf(stderr,"failed isgood: %i %i %i(%i) %i\n",m.evtnum,isgood[0],isgood[1],NGP,isgood[2]);}
    
    ++nloops;
  }
  //output end-run messages
  fprintf(stderr,"parsed %i MASTER lines\n",lines[0]);
  fprintf(stderr,"parsed %i GEANT4 lines\n",lines[1]);
  fprintf(stderr,"parsed %i SIMION lines\n",lines[2]);
  
  //  fprintf(stderr,"filled bdntree with %i beta-decay events, %i b-g, & %i b-2g, %i b-3g,& %i b-4g events\n",nbeta,nbetagamma[0]/2,nbetagamma[1]/3,nbetagamma[2]/4,nbetagamma[3]/5);


  //PRINT STATISTICS...
  
  fprintf(stderr,"\nSorted %i beta-decay events\n",nloops);

  fprintf(stderr,"Multiplicities (Rows=#gammas, Columns=#conv. electrons):");
  for(int a=0;a<MAXG;++a){
    fprintf(stderr,"\n");
    for(int b=0;b<MAXCE;++b){
      fprintf(stderr,"%i\t",nbeta[a][b]);
    }
  }
  fprintf(stderr,"\n");

  fprintf(stderr,"Singles Detected: %i betas, %i gammas, %i ce's, & %i neutrons\n",det_b,det_g,det_ce,det_n);
  fprintf(stderr,"Coincidences Detected: %i beta-gamma, %i beta-ce, %i beta-g-ce, %i beta-neutron\n",det_bg,det_bce,det_bgce,det_bn);
  
  bdntree->Write("",TObject::kOverwrite); //write TTree to ROOT File
  fprintf(stderr,"\nWrote events to \"%s\"\n",fnROOT);
  //close all files
  fclose(fSIMION);
  fclose(fGEANT);
  fclose(fMASTER);
  fROOT->Close();
  return 0;
}
