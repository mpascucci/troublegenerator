MAIN -> NL:* LINE:+ NL:? {% function(d) {return d[1]} %}
LINE -> RULE NL:+ {% function(d) {return d[0]} %}
	| COMMENT NL:+  {% function(d) {return d[0]} %}

RULE -> NAME _ ":" SEQUENTS "-->" SEQUENTS
{% function(d) {
	let type = "rule";
	if (d[3].length==0) {type='axiom'};
	return {
		type:type,
		name:d[0],
		premises:d[3],
		consequences:d[5]
	}}
%}

NAME -> [\w\d]:+ {% function(d) {return d[0].join("")} %}

SEQUENTS -> FORMULA
{% function(d) { 
	let sequents = d[0];
	let out = [];
	for (const i in sequents) {
		if (!sequents[i]) { continue };
		let sequent = sequents[i].split(';');
		let context = [];
		let active = [];
		if (sequent.length===2) {
			context = sequent[0].split(',');
			active = sequent[1].split(',');
		} else {
			active = sequent[0].split(',');
		}	
		out.push({type:"sequent", context:context, active:active});
	}
	return out;
}%}

FORMULA -> .:+ {% function(d) {
	let sequents = [];
	let t = d[0].join("").trim().split(" ") 
	for (const i in t) {
		sequents.push(t[i]);
	}
	return sequents;
}%}

COMMENT -> "#" .:* {% function(d) {return {type:"comment", text:d[1].join("")}} %}

# Whitespace. The important thing here is that the postprocessor
# is a null-returning function. This is a memory efficiency trick.
_ -> [\s]:*  {% function(d) {return null } %}
NL -> "\n" {% function(d) {return "newline" } %}