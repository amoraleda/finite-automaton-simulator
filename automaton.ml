(* Add the next state to the list of states already visited *)

let rec addPath = function (estIni,cad,[]) -> [(estIni,cad)]
	| (estIni,cad,(est2,cad2)::listRecorr) -> 
			if (estIni=est2) then (est2,cad)::listRecorr
			else (est2,cad2)::addPath(estIni,cad,listRecorr);;

let rec transitToNext = function (estIni,cad,[]) -> true
	| (estIni,cad,(est2,cad2)::listRecorr) -> 
			if (estIni=est2) & (cad=cad2) then false
			else transitToNext(estIni,cad,listRecorr);;


let rec getList = function (cad,[]) -> []
	| (cad,(cad2,listEst)::listComport) ->	if (cad=cad2) then listEst
						else getList(cad,listComport);;

let rec getNextPossibleStates = function (_,_,[]) -> []
	| (cad,estIni,(estDest,listEst)::listComport) -> 
		if (estIni=estDest) then getList(cad,listEst)
		else getNextPossibleStates(cad,estIni,listComport);;
		
		
let rec isFinalState = function (est,[]) -> false
	| (est,est2::listEstAcep) -> 	if (est=est2) then true
					else isFinalState(est,listEstAcep);;


let removeFirstElement = function [] -> []
	| (elem::listaElem) -> listaElem;;

let getFirstElement = function [] -> ""
	| elem::listaElem -> elem;;

(* Check if is possible to solve the automaton with epsilon transitions *)
let rec runOverEpsilonTransitions = function ([],automata) -> ()
	| (est::lisTVacias,(estIni,listEstAcep,listComport,recorrido,cadEntrada)) ->
		begin
			if isFinalState(est,listEstAcep) then
			begin
				print_string "With epsilon transitions accepts the state.";
				print_string est;
				print_string ".\n";
			end
			else ();	
			runOverEpsilonTransitions(lisTVacias,(estIni,listEstAcep,listComport,recorrido,cadEntrada));
			runOverEpsilonTransitions(getNextPossibleStates("tVacia",est,listComport),(est,listEstAcep,listComport,addPath(est,cadEntrada,recorrido),cadEntrada));
		end;;
		

(* Gets an initial state, list of final states, behavior, path until current state, and an input string. If the input string is empty, test if the current state is
in the list of final states. If the string is not empty, continues to the possible paths. *)

let rec solveAutomaton (estIni,listEstAcep,listComport,recorrido,cadEntrada) = 
		let rec recorrCaminos = function ([],[],automata) -> ()
			| (est::listVacios,listNVacios,(estIni,listEstAcep,listComport,recorrido,cadEntrada)) ->
				if transitToNext(est,cadEntrada,recorrido) then
				begin
					solveAutomaton(est,listEstAcep,listComport,addPath(est,cadEntrada,recorrido),cadEntrada);
					recorrCaminos(listVacios,listNVacios,(estIni,listEstAcep,listComport,recorrido,cadEntrada));
				end
				else ()

			| ([],est::listNVacios,(estIni,listEstAcep,listComport,recorrido,cadEntrada)) ->
				begin
					solveAutomaton(est,listEstAcep,listComport,addPath(est,removeFirstElement(cadEntrada),recorrido),removeFirstElement(cadEntrada));
					recorrCaminos([],listNVacios,(estIni,listEstAcep,listComport,recorrido,cadEntrada));
				end in 

		if (cadEntrada=[]) then
		begin
			if (isFinalState(estIni,listEstAcep)) then
			begin  
				print_string "The automaton accepts the input string. ";
				print_string estIni;
				print_string ".\n"
			end
			else ();
			runOverEpsilonTransitions(getNextPossibleStates("tVacia",estIni,listComport),(estIni,listEstAcep,listComport,recorrido,[]));
		end
		else recorrCaminos(getNextPossibleStates("tVacia",estIni,listComport),getNextPossibleStates(getFirstElement(cadEntrada),estIni,listComport),(estIni,listEstAcep,listComport,recorrido,cadEntrada));;


let rec existElement =  function (elem1,[]) -> [elem1]
	| (elem1,elem2::listaElem) -> 
		if (elem1=elem2) then listaElem
		else elem2::existElement(elem1,listaElem);;



let rec searchEquivalent = function (estFin,cad1,[]) ->[(cad1,[estFin])] 
	| (estFin,cad1,(cad2,listEst)::listTup) ->	
		if (cad1=cad2) then (cad2,existElement(estFin,listEst))::listTup
		else (cad2,listEst)::searchEquivalent(estFin,cad1,listTup);;

let rec insertState = function (estIni,estFin,[])-> [(estFin,[])]
	|(estIni,estFin,(est,listTup)::listAut) -> 	if (estIni=estFin) then (est,listTup)::listAut
							else (est,listTup)::insertState(estIni,estFin,listAut);; 


let rec validateTuple = function (estIni,estFin,cad,[]) ->[(estIni,[(cad,[estFin])]);(estFin,[])]
	| (estIni,estFin,cad,(est1,listTup)::listAut) -> 	
		if (estIni=est1) then (est1,searchEquivalent(estFin,cad,listTup))::insertState(estIni,estFin,listAut)
		else (est1,listTup)::validateTuple(estIni,estFin,cad,listAut);;
								
								
let rec readStartState () =
	begin
		print_string "\n - Input a start state: ";
		let entr=read_line() in
		if entr="" then readStartState()
		else entr
	end;;

let rec readFinishState () =
	begin
		print_string "\n - Input a finish state: ";
		let entr=read_line() in
		if entr="" then readFinishState()
		else entr
	end;;

let transitionSigma () =
	begin
		print_string "\n - Transition string to reach the state (epsilon transition press enter): ";
		let entr=read_line() in
		if entr="" then "tVacia"
		else entr
	end;;


let rec readAutomatonBehavior(lTupla) = let estIni=readStartState() and estFin=readFinishState() and cad=transitionSigma () in
	begin
		print_string "\n More input? (y/n): ";
		if (read_line() = "n") then validateTuple(estIni,estFin,cad,lTupla)
		else readAutomatonBehavior(validateTuple(estIni,estFin,cad,lTupla));
	end;;


let rec getStatesList = function [] -> []
	| (est,lisEsta)::listCompor ->est::(getStatesList listCompor);;


let isStateValid = isFinalState;;


let rec readInitialState (lista) = 
	begin
		print_string "\n - Write initial state: ";
		let entr=read_line() in 
		if isStateValid(entr,lista) then  entr
		else
		begin
			print_string"\n - Warning: write an existing state.\n";
			readInitialState(lista);
		end;
	end;;


let rec addToList car = function [] -> [car]
	| elem::lista -> 	if (car=elem) then elem::lista
				else elem::(addToList car lista);;


let rec getAllSigmas= function [] -> []
	| (est,[])::listComp -> getAllSigmas(listComp)
	| (est,(car,listEst)::listaTupl)::listComp ->addToList car (getAllSigmas((est,listaTupl)::listComp));;


let rec readInput (lista) =
	begin
		print_string "\n - Input string to test the automaton (Press enter to finish):  \n";
		let entr=read_line() in
		if isStateValid(entr,lista) then entr::readInput(lista)
		else if entr="" then []
		else 
		begin
			print_string "\n - Warning: please enter a valid input string.\n";
			readInput(lista);
		end;
	end;; 

let rec readFinalStates (lista) =
	begin
		print_string "\n - Enter valid final states (Press enter to finish): \n";
		let entr=read_line() in
		if isStateValid(entr,lista) then entr::readFinalStates(lista)
		else if entr="" then []
		else 
		begin
			print_string "\n - Warning: Input finish state.\n";
			readFinalStates(lista);
		end;
	end;; 			 


let constructTuple (comport,lista) = let estIni=readInitialState(lista) and estAcept=readFinalStates(getStatesList(comport)) and cadDisp=readInput(getAllSigmas(comport)) in solveAutomaton(estIni,estAcept,comport,[(estIni,cadDisp)],cadDisp);;


(* MAIN *)
let rec mainProgram()= let comport=readAutomatonBehavior([]) in 
	begin
		constructTuple(comport, getStatesList comport);
		print_string "\n Close program ? (y/n)";
		let entr=read_line() in
		if entr="y" then ()
		else mainProgram()
	end;;