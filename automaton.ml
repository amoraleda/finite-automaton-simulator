(*Esta funcion tiene como parámetros el estado al que vamos a pasar, la cadena de entrada por la
 que nos encontramos y el recorrido llevado hasta ahora. Lo que hace es comprobar si ya hemos
 pasado por dicho estado y si hemos pasado, modifica la cadena con la que habíamos pasado 
 anteriormente, si no habíamos pasado, añade el estado y la cadena actual a la lista de recorrido*)

let rec addPath = function (estIni,cad,[]) -> [(estIni,cad)]
	| (estIni,cad,(est2,cad2)::listRecorr) -> 
			if (estIni=est2) then (est2,cad)::listRecorr
			else (est2,cad2)::addPath(estIni,cad,listRecorr);;


(*Recibe el estado al que vamos a pasar, la cadena de entrada actual y una lista con el recorrido
 que hemos realizado hasta el momento. Si no hemos pasado por ese estado o hemos pasado con una
 cadena diferente devuelve true, si hemos pasado con la misma cadena devuelve false*)

let rec transitToNext = function (estIni,cad,[]) -> true
	| (estIni,cad,(est2,cad2)::listRecorr) -> 
			if (estIni=est2) & (cad=cad2) then false
			else transitToNext(estIni,cad,listRecorr);;


(*Recibe una cadena y una lista de estados disponibles del automata desde el estado actual. Compara
 la cadena con el primer elemento de la tupla de cada elemento de la lista y si es igual, devuelve
 el segundo elemento, que es una lista con todos los estados accesibles desde el estado actual 
 con la cadena de entrada *)

let rec getList = function (cad,[]) -> []
	| (cad,(cad2,listEst)::listComport) ->	if (cad=cad2) then listEst
						else getList(cad,listComport);;


(*Recibe un symbol de entrada y un autómata. Da la lista de los posibles estados a los que puede 
 pasar con dicho símbolo desde el estado en el que nos encontramos*)

let rec getPossibleStates = function (_,_,[]) -> []
	| (cad,estIni,(estDest,listEst)::listComport) -> 
		if (estIni=estDest) then getList(cad,listEst)
		else getPossibleStates(cad,estIni,listComport);;
		
		
(*Recibe un estado y una lista de estados aceptadores y comprueba que el estado que le hemos 
 pasado es un aceptador o no*)

let rec isFinalState = function (est,[]) -> false
	| (est,est2::listEstAcep) -> 	if (est=est2) then true
					else isFinalState(est,listEstAcep);;


(*Recibe una lista y quita el primer elemento. Si la lista está vacía devuelve la lista vacía*)

let removeFirstElement = function [] -> []
	| (elem::listaElem) -> listaElem;;


(*Recibe un lista y devuelve el primer elemento de la cadena de entrada. Si la lista está vacía 
 devuelve caracter en blanco*)

let getFirstElement = function [] -> ""
	| elem::listaElem -> elem;;


(*Recibe una lista de los caminos a seguir mediante transiciones vacías y un autómata. Una vez que se haya acabado la cadena
 de entrada, miramos las posibles soluciones únicamente con las transiciones vacías*)

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
			runOverEpsilonTransitions(getPossibleStates("tVacia",est,listComport),(est,listEstAcep,listComport,addPath(est,cadEntrada,recorrido),cadEntrada));
		end;;
		

(*Recibe como entrada un autómata compuesto de estado inicial, lista de estados aceptadores, comportamiento, 
 recorrido hasta el momento y cadena de entrada. Si la cadena de entrada es vacia, mira si el estado en el que
 nos encontramos es aceptador. Si la cadena no es vacia transitToNext los caminos posibles*)

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
				print_string "The automaton accepts the input string.";
				print_string estIni;
				print_string ".\n"
			end
			else ();
			runOverEpsilonTransitions(getPossibleStates("tVacia",estIni,listComport),(estIni,listEstAcep,listComport,recorrido,[]));
		end
		else recorrCaminos(getPossibleStates("tVacia",estIni,listComport),getPossibleStates(getFirstElement(cadEntrada),estIni,listComport),(estIni,listEstAcep,listComport,recorrido,cadEntrada));;



(*Buscamos un elemento en una lista, si no está lo metemos, si está no hacemos nada*)

let rec existElement =  function (elem1,[]) -> [elem1]
	| (elem1,elem2::listaElem) -> 
		if (elem1=elem2) then listaElem
		else elem2::existElement(elem1,listaElem);;



(* Aumentamos el comportamiento del aut—mata *)

let rec searchEquivalent = function (estFin,cad1,[]) ->[(cad1,[estFin])] 
	| (estFin,cad1,(cad2,listEst)::listTup) ->	
		if (cad1=cad2) then (cad2,existElement(estFin,listEst))::listTup
		else (cad2,listEst)::searchEquivalent(estFin,cad1,listTup);;

(* Introducimos en el comportamiento los estados que no tienen flechas de salida *)
let rec insertState = function (estIni,estFin,[])-> [(estFin,[])]
	|(estIni,estFin,(est,listTup)::listAut) -> 	if (estIni=estFin) then (est,listTup)::listAut
							else (est,listTup)::insertState(estIni,estFin,listAut);; 


	
(* Validate tuple *)
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