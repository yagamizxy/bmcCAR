/*
    Copyright (C) 2018, Jianwen Li (lijwen2748@gmail.com), Iowa State University

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

/*
	Author: Jianwen Li
	Update Date: October 6, 2017
	Main Solver in CAR
*/


#include "mainsolver.h"
#include "data_structure.h"
#include "utility.h"

#include <algorithm>
using namespace std;

namespace car
{
	//int MainSolver::max_flag_ = -1;
	//vector<int> MainSolver::frame_flags_;
	
	MainSolver::MainSolver (Model* m, Statistics* stats, const bool verbose) 
	{
	    verbose_ = verbose;
	    stats_ = stats;
		model_ = m;
		current_unroll_level_ = 1; //default unrolling level is 1
		max_unroll_level_ = m->get_max_unroll();
		init_flag_ = m->max_id()*(max_unroll_level_+1) + 1;
		dead_flag_ = m->max_id ()*(max_unroll_level_+1) + 2;
		max_flag_ = m->max_id()*(max_unroll_level_+1) + 3;
	    //constraints
		for (int i = 0; i < m->outputs_start (); i ++)
			add_clause (m->element (i));
		//outputs
		for (int i = m->outputs_start (); i < m->latches_start (); i ++)
			add_clause (m->element (i));
		//latches
		for (int i = m->latches_start (); i < m->size (); i ++)
		    add_clause (m->element (i));
		unroll_to_level(max_unroll_level_);
	}
	
	void MainSolver::set_assumption (const Assignment& st, const int id)
	{
		assumption_.clear ();
		assumption_push (id);
		
		for (Assignment::const_iterator it = st.begin (); it != st.end (); it++)
		{
			assumption_push (*it);
		}		
	}
	
	void MainSolver::set_assumption (const Assignment& a,const int bad,const int frame_level, const bool forward,const int unroll_lev)
	{
		assumption_.clear ();
		if (frame_level > 0)
			assumption_push (flag_of (frame_level,unroll_lev));	
		else if(frame_level == 0)
			assumption_push(model_->prime(bad,unroll_lev));
		for (Assignment::const_iterator it = a.begin (); it != a.end (); it ++)
		{
			int id = *it;
			if (forward)
				assumption_push (model_->prime (id,unroll_lev));
			else
				assumption_push (id);
		}
			
	}
	void MainSolver::unroll_to_level(const int level){
		for(int lev = current_unroll_level_+1; lev <= level; lev++){

			for (int i = 0; i < model_->outputs_start (); i ++){
				vector<int> tmp = model_->clause_prime(i,lev);
				add_clause (tmp);
			}
				
			//outputs
			for (int i = model_->outputs_start (); i < model_->latches_start (); i ++){
				vector<int> tmp = model_->clause_prime(i,lev);
				add_clause (tmp);
			}
			//latches
			for (int i = model_->latches_start (); i < model_->size (); i ++){
				vector<int> tmp = model_->clause_prime(i,lev);
				add_clause (tmp);
			}
			add_unroll_level();
		}
		
	}
	
	Assignment MainSolver::get_state (const bool forward, const bool partial)
	{
		Assignment model = get_model ();
		shrink_model (model, forward, partial);
		return model;
	}
	
	std::vector<Cube> MainSolver::get_state_vector (int unroll_level)
	{
		Assignment model = get_model ();
		std::vector<Cube> res = shrink_model_vector (model,unroll_level);
		return res;
	}

	//this version is used for bad check only
	Cube MainSolver::get_conflict (const int bad)
	{
		Cube conflict = get_uc ();
		Cube res;
		for (int i = 0; i < conflict.size (); i ++)
		{
			if (conflict[i] != bad)
				res.push_back (conflict[i]);
		}
		
		std::sort (res.begin (), res.end (), car::comp);
		return res;
	}
	
	Cube MainSolver::get_conflict (const bool forward, const bool minimal, bool& constraint,const int unroll_lev)
	{
		Cube conflict = get_uc ();
		
		if (minimal)
		{
			stats_->count_orig_uc_size (int (conflict.size ()));
			try_reduce (conflict);
			stats_->count_reduce_uc_size (int (conflict.size ()));
		}
		
			
		if (forward)
		    model_->shrink_to_previous_vars (conflict, constraint,unroll_lev);
		else
		    model_ -> shrink_to_latch_vars (conflict, constraint);
		
		
		std::sort (conflict.begin (), conflict.end (), car::comp);
		
		return conflict;
	}
	
	void MainSolver::add_new_frame (const Frame& frame, const int frame_level, const bool forward)
	{
		for (int i = 0; i < frame.size (); i ++)
		{
			add_clause_from_cube (frame[i], frame_level, forward);
		}
	}
	
	void MainSolver::add_clause_from_cube (const Cube& cu, const int frame_level, const bool forward,int unroll_level)
	{
		int flag = flag_of (frame_level,unroll_level);//flag_of (frame_level,unroll_level)
		// cout<<"flag: "<<flag<<endl;
		// cout<<"frame_level: "<<frame_level<<endl;
		// cout<<"unroll_level: "<<unroll_level<<endl;
		// car::print(cu);
		vector<int> cl;
		cl.push_back (-flag);
		for (int i = 0; i < cu.size (); i ++)
		{
			cl.push_back (-model_->prime (cu[i],unroll_level));
		}
		add_clause (cl);
	}
	
	void MainSolver::shrink_model (Assignment& model, const bool forward, const bool partial)
	{
	    Assignment res;
	    
	    for (int i = 0; i < model_->num_inputs (); i ++)
	    {
	        if (i >= model.size ())
	        {//the value is DON'T CARE, so we just set to 0
	            res.push_back (0);
	        }
	        else
	            res.push_back (model[i]);
	    }
	        
		if (forward)
		{
		    for (int i = model_->num_inputs (); i < model_->num_inputs () + model_->num_latches (); i ++)
		    {   //the value is DON'T CARE 
		        if (i >= model.size ())
		            break;
		        res.push_back (model[i]);
		    }
		    if (partial)
		    {
		        //TO BE DONE
		    }
		}
		else
		{
		    Assignment tmp;
		    tmp.resize (model_->num_latches (), 0);
		    for (int i = model_->num_inputs ()+1; i <= model_->num_inputs () + model_->num_latches (); i ++)
		    {
		    	
		    	int p = model_->prime (i);
		    	assert (p != 0);
		    	assert (model.size () > abs (p));
		    	
		    	int val = model[abs(p)-1];
		    	if (p == val)
		    		tmp[i-model_->num_inputs ()-1] = i;
		    	else
		    		tmp[i-model_->num_inputs ()-1] = -i;
		    }
		    
		    		    
		    for (int i = 0; i < tmp.size (); i ++)
		        res.push_back (tmp[i]);
		    if (partial)
		    {
		        //TO BE DONE
		    }
		}
		model = res;
	}
	
	std::vector<Cube> MainSolver::shrink_model_vector (Assignment& model,int unroll_level)
	{
		Frame res;
		for(int lev = 1; lev <= unroll_level; ++lev){
			Cube element;
			for (int i = model_->prime(0,lev); i < model_->prime(model_->num_inputs (),lev); i ++)
			{
				if (i >= model.size ())
				{//the value is DON'T CARE, so we just set to 0
					element.push_back (0);
				}
				else{
					// if(model[i] < 0) 
					// 	cout<<model[i]<<endl;
					element.push_back (model_->previous(model[i],lev));
				}
					
			}
				
			int latch_start = model_->prime(model_->num_inputs (),lev);
			int latch_end = model_->prime(model_->num_inputs ()+model_->num_latches (),lev);
			for (int i = latch_start; i < latch_end; i ++)
			{
				assert (i != 0);
				assert (model.size () > abs (i));
				element.push_back (model_->previous(model[i],lev));
			}
			res.push_back(element);
			
		}
		return res;
	    
	}

	void MainSolver::try_reduce (Cube& cu)
	{
		
	}
	
	
}
