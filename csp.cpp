#include "csp.h"
#include <climits>

#ifdef INLINE_CSP
//#warning "INFO - inlining CSP methods"
#define INLINE inline
#else   
//#warning "INFO - NOT inlining CSP methods"
#define INLINE 
#endif


////////////////////////////////////////////////////////////
//CSP constructor
template <typename T>
CSP<T>::CSP(T& cg) :
	arc_consistency(),
	cg(cg),
	solution_counter(0),
	recursive_call_counter(0),
	iteration_counter(0)
{
}
////////////////////////////////////////////////////////////
//CSP solver, brute force - no forward checking
template <typename T>
bool CSP<T>::SolveDFS(unsigned level)
{
	++recursive_call_counter;
	
	if (cg.AllVariablesAssigned())
	{
		++solution_counter;
		return true;
	}
	
	Variable* var_to_assign = MinRemVal();
	std::set<Value> domain = var_to_assign->GetDomain();
	
	for (int i = 0; i < var_to_assign->SizeDomain(); ++i)
	{
		++iteration_counter;
		var_to_assign->Assign();
		
		if (AssignmentIsConsistent(var_to_assign))
		{
			if(SolveDFS(level + 1))
			{
				return true;
			}
		}
		
		var_to_assign->RemoveValue(var_to_assign->GetValue());
		var_to_assign->UnAssign();
		
		--i;
		
		if (var_to_assign->IsImpossible())
		{
			var_to_assign->SetDomain(domain);
			return false;
		}
	}
	
	return false;

}


////////////////////////////////////////////////////////////
//CSP solver, uses forward checking
template <typename T>
bool CSP<T>::SolveFC(unsigned level)
{
	++recursive_call_counter;
	
	if (cg.AllVariablesAssigned())
	{
		++solution_counter;
		return true;
	}
	
	Variable* var_to_assign = MinRemVal();
	auto state = SaveState(var_to_assign);
	
	for (int i = 0; i < var_to_assign->SizeDomain(); ++i)
	{
		++iteration_counter;
		var_to_assign->Assign();
		
		if (AssignmentIsConsistent(var_to_assign) && ForwardChecking(var_to_assign))
		{
			if(SolveFC(level + 1))
			{
				return true;
			}
		}
		
		LoadState(state);
		var_to_assign->RemoveValue(var_to_assign->GetValue());
		var_to_assign->UnAssign();
		
		--i;
		
		if (var_to_assign->IsImpossible())
		{
			return false;
		}
	}
	return false;
}
////////////////////////////////////////////////////////////
//CSP solver, uses arc consistency
template <typename T>
bool CSP<T>::SolveARC(unsigned level)
{
	//placeholder to pass error test
	level = 0;
	unsigned a = level;
	a += a;
	return false;
}


template <typename T>
INLINE
bool CSP<T>::ForwardChecking(Variable* x)
{
	auto neighbors = cg.GetNeighbors(x);
	
	for (auto n : neighbors)
	{
		if (n->IsAssigned())
		{
			continue;
		}
		
		auto constraints = cg.GetConnectingConstraints(x, n);
		
		for (auto c : constraints)
		{
			auto domain = n->GetDomain();
			for(auto d : domain)
			{
				n->Assign(d);
				if(!(c->Satisfiable()))
				{
					n->RemoveValue(d);
				}
				n->UnAssign();
			}
			if(n->SizeDomain() == 0)
			{
				if (n->IsImpossible())
				{
					return false;
				}
			}
		}
	}
	return true;
}
////////////////////////////////////////////////////////////
//load states (available values) of all unassigned variables 
template <typename T>
void CSP<T>::LoadState(
	std::map<Variable*, std::set<typename CSP<T>::Variable::Value> >& saved) const
{
	typename std::map<Variable*, std::set<typename Variable::Value> >::iterator
		b_result = saved.begin();
	typename std::map<Variable*, std::set<typename Variable::Value> >::iterator
		e_result = saved.end();

	for (; b_result != e_result; ++b_result) 
	{
		(*b_result).first->SetDomain((*b_result).second);
	}
}


////////////////////////////////////////////////////////////
//save states (available values) of all unassigned variables 
//except the current
template <typename T>
INLINE
std::map< typename CSP<T>::Variable*, std::set<typename CSP<T>::Variable::Value> >
CSP<T>::SaveState(typename CSP<T>::Variable* x) const {
	std::map<Variable*, std::set<typename Variable::Value> > result;

	const std::vector<Variable*>& all_vars = cg.GetAllVariables();
	typename std::vector<Variable*>::const_iterator
		b_all_vars = all_vars.begin();
	typename std::vector<Variable*>::const_iterator
		e_all_vars = all_vars.end();
	for (; b_all_vars != e_all_vars; ++b_all_vars) {
		if (!(*b_all_vars)->IsAssigned() && *b_all_vars != x) {
			//std::cout << "saving state for " 
			//<< (*b_all_vars)->Name() << std::endl;
			result[*b_all_vars] = (*b_all_vars)->GetDomain();
		}
	}
	return result;
}
////////////////////////////////////////////////////////////
//check the current (incomplete) assignment for satisfiability
template <typename T>
INLINE
bool CSP<T>::AssignmentIsConsistent(Variable* p_var) const
{
	auto constraints = cg.GetConstraints(p_var);

	for (auto c : constraints) 
	{
		if(c->Satisfiable() == false)
		{
			return false;
		}
	}

	return true;
}
////////////////////////////////////////////////////////////
//insert pair 
//(neighbors of the current variable, the current variable)
//current variable is th variable that just lost some values
// for all y~x insert (y,x)
//into arc-consistency queue

//template <typename T>
//INLINE
//void CSP<T>::InsertAllArcsTo(Variable* cv)
//{
//}
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
//AIMA p.209 AC-3 algorithm
template <typename T>
INLINE
bool CSP<T>::CheckArcConsistency(Variable* x)
{
	return false;
}
////////////////////////////////////////////////////////////
//CHECK that for each value of x there is a value of y 
//which makes all constraints involving x and y satisfiable
//template <typename T>
//INLINE
//bool CSP<T>::RemoveInconsistentValues(Variable* x, Variable* y, const Constraint* c)
//{
//
//
//
//
//
//
//
//
//
//
//
//}
////////////////////////////////////////////////////////////
//choose next variable for assignment
//choose the one with minimum remaining values
template <typename T>
INLINE
typename CSP<T>::Variable* CSP<T>::MinRemVal()
{
	std::vector<Variable*> variables = cg.GetAllVariables();
	typename std::vector<Variable*>::const_iterator iter = variables.begin();
	typename std::vector<Variable*>::const_iterator end = variables.end();
	
	Variable* min = (*iter);
	int minimum = INT_MAX;
	
	for (	; iter != end; ++iter) 
	{
		if (!(*iter)->IsAssigned())
		{
			int currSize = (*iter)->SizeDomain();
			if(currSize < minimum)
			{
				minimum = currSize;
				min = (*iter);
			}
		}
	}
	return min;
}
////////////////////////////////////////////////////////////
//choose next variable for assignment
//choose the one with max degree
template <typename T>
typename CSP<T>::Variable* CSP<T>::MaxDegreeHeuristic()
{
	std::vector<Variable*> variables = cg.GetAllVariables();
	typename std::vector<Variable*>::const_iterator begin = variables.begin();
	typename std::vector<Variable*>::const_iterator end = variables.end();
	
	Variable* max = nullptr;
	unsigned maxDegree = INT_MIN;
	
	for (	; begin != end; ++begin) 
	{
		const unsigned currDegree = cg.GetNeighbors((*begin)).size();
		if(maxDegree < currDegree)
		{
			maxDegree = currDegree;
			max = (*begin);
		}
	}
	return max;
}


#undef INLINE_CSP
