module ParamGen

// Structure  ------------------------------------------

sig Value {}

abstract sig Key {
	var map : lone Dict+Value
}

sig Dict {
	contents: set Key
}

sig Label extends Key {}
sig Guard extends Key {}
sig Root extends Key {}{
	no this.~contents
}

one sig Null extends Value {}

var sig VarsToExpand in Label+Guard+Value {}

// Constraints  ------------------------------------------

pred invariants{

	// map.*contents relation is acyclic
	no iden & ^(map.*contents)

	all i: Dict+Value |
		// each item can have at most one key
		lone i.~map

	all k: Key |
		// each key can be contained by only one dict
		lone k.~contents

	all d: Dict | 
		// if one content is a guard, all contents must be guards
		{some Guard & d.contents implies d.contents in Guard}

	// Value rules
	all v: Value | 
		// all values must be preceded by a label
		some v.^(~map.*~contents) & Label // THIS IS NOT CHECKED IN IMPLEMENTATION

}

fact initialConditions{

	invariants and

	all k: Key |
		// all keys should lead to a value
		{some k.^(map.*contents) & Value} and

		// all keys should be accessible from some root
		{some k.*(~contents.*~map) & Root}
}

fact validTransitions{
	// If an item doesn't initially have variables to expand, it can't have variables to expand in the next state
	all i: Label+Guard+Value | i not in VarsToExpand implies i not in VarsToExpand'
	
   // Unless an item is a dictionary containing guards, its key cannot change at the next state
	all i: Dict+Value | i not in Dict implies i.~map = i.~map' 
}


// Dynamics  ------------------------------------------

pred is_guarded_dict[d: Dict] {
	d.contents in Guard
}

pred reduce[r: Root] {

	// No changes for others:
	{all ro: Root-r |
		all k: ro.*map.*contents & Key | k.map' = k.map
	}

	// No change in root dict if it's not a guarded dict
	not is_guarded_dict[r.map] implies r.map = r.map' 

	// now call reduce for root dict
	reduce[r.map]
}


pred impose_guards[d: Dict]{
	let pkey = d.~map {
		some g: d.contents {
			pkey.map' = g.map and
			g.map' = none
			(d.contents-g).map' = (d.contents-g).map
			reduce[pkey.map']
		}
	}
}


let expand_vars[data]{
  no data & VarsToExpand'
}


pred reduce[data: Dict+Value]{

	data in Dict implies {

		// (1) Expand vars in keys
		expand_vars[data.contents]

		// (2) Evaluate guards
		is_guarded_dict[data] implies
			impose_guards[data]

		// (3) Call reduce for all branches
		else
			all key : data.contents |
				key.map' = key.map and 
					reduce[key.map']
	}
	else
		// (4) Expand vars
		expand_vars[data]
}


// Safety  ------------------------------------------

pred reduce_is_safe[r:Root] {

	reduce[r] implies {

		// All invariants still remain true
		invariants and

		// The result of postcondition should be a dict
		r.map' in Dict

		// check properties of active columns
		all ai:  r.*(map'.*contents) {
			
			// all labels map to some Values or Dictionaries
			{ai in Label implies ai.map in Value+Null+Dict}

			// no active guard remains
			ai not in Guard

			// all keys should lead to a value
			{ai in Key implies some ai.^(map.*contents) & Value}

			// all values should have a label (varname)
			{ai in Value implies some ai.^(~map.*~contents) & Label}

			// no remaining vars to expand
			ai not in VarsToExpand'

		}
	}
}

assert postconditions {
	all r: Root | 
		reduce_is_safe[r]
}

check postconditions for 8 but 2 steps

// Simulate  ------------------------------------------

run {
	some VarsToExpand&Label and //todo remove this
	some r:Root |
		some Guard & r.^(map.*contents) and
		reduce[r]

} for 4 but 8 Key, 1 Root , 2 steps
