import java.io.*;
import java.net.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*
   VERIFAST Concurrent Statistics Web Server Sample Code
   CVS course 14-15
   Integrated Master in Computer Science and Engineering
   @FCT UNL Luis Caires 2015
   */

/*@
  predicate ElemP(unit info, Pair item; unit o) =
  item != null &*& PairInv(item) &*& o == unit;

  predicate StatisticsInv(Statistics st;int n) =
  st.store |-> ?s
  &*&
  s != null
  &*&
  st.nelems |-> n
  &*&
  st.storeSize |-> ?sz &*&
  sz == s.length
  &*&
  n <= sz
  &*&
  array_slice_deep(s,0,n,ElemP,unit,_,_) &*&
  array_slice(s,n,s.length,?r)
  &*& all_eq(r,null) == true;

  predicate_ctor Pair_shared_state (Pair p) () =
  p.count |-> ?n &*& n>= 0 &*& p.name |-> ?s &*& s != null;

  predicate PairInv (Pair p;) =
  p.mon |-> ?l &*& l != null &*& lck(l,1,Pair_shared_state(p));

  @*/

class Pair {

  String name;
  int count;
  ReentrantLock mon;

  public Pair(String n, int c)
    //@ requires n != null && c >= 0;
    //@ ensures PairInv(this);
  {
    name = n;
    count = c;
    //@ close Pair_shared_state(this)();
    //@ close enter_lck(1,Pair_shared_state(this));
    mon = new ReentrantLock();
    //@ close PairInv(this);
  }

  String getN()
    //@ requires [?f]PairInv(this);
    //@ ensures [f]PairInv(this) &*& result != null;
  {
    String r;
    //@ open [f]PairInv(this);
    mon.lock();
    //@ open Pair_shared_state(this)();
    r = name;
    //@ close Pair_shared_state(this)();
    mon.unlock();
    //@ close [f]PairInv(this);
    return r;
  }

  int getC()
    //@ requires [?f]PairInv(this);
    //@ ensures [f]PairInv(this);
  {
    int r;
    //@ open [f]PairInv(this);
    mon.lock();
    //@ open Pair_shared_state(this)();
    r = count;
    //@ close Pair_shared_state(this)();
    mon.unlock();
    //@ close [f]PairInv(this);
    return r;
  }

  void inc()
    //@ requires [?f]PairInv(this);
    //@ ensures [f]PairInv(this);
  {
    //@ open PairInv(this);
    mon.lock();
    //@ open Pair_shared_state(this)();
    count++;
    //@ close Pair_shared_state(this)();
    mon.unlock();
    //@ close [f]PairInv(this);
  }

}

public class Statistics {

  Pair store[];
  int nelems;
  int storeSize;

  public Statistics(int size)
    //@ requires size > 0;
    //@ ensures StatisticsInv(this,0);
  {
    store = new Pair[size];
    storeSize = size;
    nelems = 0;
  }

  public String collect()
    //@ requires [?f]StatisticsInv(this,?n);
    //@ ensures [f]StatisticsInv(this,n) &*& result != null;
  {
    int i = 0;
    String ans  = new String();
    //@ open StatisticsInv(this,n);
    while (i<nelems)
      /*@ invariant [f]store |-> ?s &*& s != null &*&
        [f]nelems |-> n &*& [f]storeSize |-> ?sz &*& sz == s.length &*& n <= sz
        &*& [f]array_slice_deep(s,0,n,ElemP,unit,_,_) &*&
        [f]array_slice(s,n,s.length,?r)
        &*& all_eq(r,null) == true &*&
        0<=i &*& i<=n &*& ans != null;
        @*/
    {
      Integer.toString(store[i].getC());
      ans = ans + store[i].getN()+":"+ Integer.toString(store[i].getC())+"<p>";
      i++;
    }
    return ans;
  }

  public void log(String fn)
    //@ requires [?f]StatisticsInv(this,?n) &*& fn != null;
    //@ ensures [f]StatisticsInv(this,?nn) &*& (n==nn||nn==n+1);
  {
    int i = 0;
    //@ open StatisticsInv(this,n);
    while (i<nelems)
      /*@ invariant [f]store |-> ?s &*& s != null &*&
        [f]nelems |-> n &*& [f]storeSize |-> ?sz &*& sz == s.length &*& n <= sz
        &*& [f]array_slice_deep(s,0,n,ElemP,unit,_,_) &*&
        [f]array_slice(s,n,s.length,?r)
        &*& all_eq(r,null) == true &*&
        0<=i &*& i<=n;
        @*/
    {
      if(store[i].getN().equals(fn)) {
        store[i].inc();
        break;
      };
      i++;
    }
    if(i<nelems) {
      // log capacity exceeded, ignore
    } else
      if(nelems < storeSize) {
        store[nelems]  = new Pair(fn,0);
        //@ array_slice_deep_close(store, nelems, ElemP, unit);
        nelems ++;
      }
  }

}
