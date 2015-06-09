/*
   VERIFAST Concurrent Statistics Web Server Sample Code
   CVS course 14-15
// based on h.java
//------------------------------------------
Integrated Master in Computer Science and Engineering
@FCT UNL Luis Caires 2015
*/

import java.io.*;
import java.net.*;
import java.util.*;

/*@
  predicate Listener_shared_state (Listener l;) =
  l.stat |-> ?b &*& b != null &*& l.ff |-> ?f &*& [f]StatisticsInv(b,_) &*&
  l.c |-> ?s &*& s.Socket(?i, ?o) &*& s != null &*& i.InputStream() &*& o.OutputStream();

  predicate Buffer_frac(real f) = true;
  @*/

class Listener implements Runnable {

  //@ predicate pre() = Listener_shared_state(this);
  //@ predicate post() = true;

  //@ real ff;

  private Statistics stat;
  private Socket c;

  public Listener(Socket s, Statistics b)
    /*@
      requires b != null &*& Buffer_frac(?f) &*& [f]StatisticsInv(b,_) &*& s != null &*& s.Socket(?i,?o)
      &*& i.InputStream() &*& o.OutputStream(); @*/
    //@ensures Listener_shared_state(this);
  {

    //@ ff = f;
    stat = b;
    c = s;
    //@ close Listener_shared_state(this);

  }

  public void run()
    //@ requires pre();
    //@ ensures post();
  {
    //@ open pre();
    //@ open Listener_shared_state(this);
    {
      try {
        BufferedReader i = new BufferedReader(new InputStreamReader(c.getInputStream()));
        DataOutputStream o = new DataOutputStream(c.getOutputStream());

        try{
          String s = i.readLine();
          if(s.length() > 0)
          {
            if(s.startsWith("GE")){
              String ss[] = s.split(" ");
              if (ss.length > 1) {
                String p = ss[1];
                String r = p;
                if(p != null){
                  p = ("." + (p.endsWith("/") ? p + "index.html" : p)).replace('/', File.separatorChar);
                  if(r.equals("/statistics")) {
                    String ans = stat.collect();
                    o.writeBytes("HTTP/1.0 200 OK\nContent-type: text/html\n");
                    o.writeBytes("Content-Length:"+Integer.toString(ans.length()+40)+"\n\n");
                    o.writeBytes("<h1>Statistics</h1>");
                    o.writeBytes(ans);
                  } else {
                    File f = new File(p);
                    int l = (int) f.length();
                    if (l==0) {
                      o.writeBytes("HTTP/1.0 200 OK\nContent-type: text/html\n");
                      o.writeBytes("Content-Length:40\n\n");
                      o.writeBytes("<h1>File Not Found</h1>\n\n");
                    } else {
                      byte[] b = new byte[l];
                      new FileInputStream(p).read(b);
                      o.writeBytes("HTTP/1.0 200 OK\nContent-type: text/html\n");
                      o.writeBytes("Content-Length:" + Integer.toString(l) + "\n\n");
                      o.write(b, 0, l);
                      //stat.log(p);
                    }
                  }
                }

              }
            }
          }
          o.close();
        } catch(Exception e){
        }
      } catch(Exception e){
      }
    }
    //@ close post();
  }
}

public class httpdx
{
  public static final int SOCKET = 8181;
  public static final int LOGSIZE = 256;
  public static void main(String[] args)
    //@requires true;
    //@ensures true;
  {

    Statistics acc = new Statistics(LOGSIZE);
    //@ close StatisticsInv(acc,0);
    //@ real remain = 1;

    try {
      ServerSocket ss = new ServerSocket(SOCKET);
      for(;;)
        //@ invariant [remain]StatisticsInv(acc,_) &*& ss.ServerSocket() ;
      {
        Socket s = ss.accept();
        //@ close Buffer_frac(remain/2);
        //@ remain = remain / 2;
        (new Thread(new Listener(s,acc))).start();
      }
    } catch(Exception e){}
  }

}

