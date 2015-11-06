// SIGNATURES


sig User {
						
				}

sig Passenger extends User{
					activeCall: lone CallRequest,
					books:set Reservation,
}

sig TaxiDriver extends User{

					activeCall: lone CallRequest,
					exceptionRaised:set TaxiException
}

one sig Place{}

one sig City {
	zones: some Zone
}

sig Zone {
	taxiQueue: one TaxiQueue
}

sig TaxiQueue {
	taxiList: set TaxiDriver,	
}

sig CallRequest {
	
	recap: one RunInfo,
	
}

sig Reservation{
    departure: one Place,
    arrival: one Place,
	call: lone CallRequest,
}

sig RunInfo{
					departure: one Place,
					arrival: lone Place,
					}

sig Exception{}

sig TaxiException extends Exception{
					
					related:CallRequest
				

}






// FACTS

fact OneCityPerZone{
	// every zone has exactly 1 city
	all z: Zone | (one c: City | z in c.zones)
}

fact OneZonePerQueue{
	// every queue has exactly 1 zone
	all q: TaxiQueue | (one z: Zone | z.taxiQueue = q)
}

fact OneQueuePerDriver{
	// ogni driver appartiene ad una sola queue
	all t: TaxiDriver | (lone q: TaxiQueue | t in q.taxiList)
}

fact OneRunInfoPerCall{
	all i: RunInfo | one c: CallRequest |  i= c.recap } //for every CallRequest must be only one RunInfo



fact OneDriverForCall{ //One TaxiDriver can have at most one ActiveCall
	
		all t: TaxiDriver | #(t.activeCall)<2

}



fact NoDriverBusyOnQueue{
//if a TaxiDrives has an active call ,he is  not in any TaxiQueue
no t:TaxiDriver  |(#(t.activeCall)=1 and (some q:TaxiQueue | t  in q.taxiList ))
}


fact ReservationProperties{


			//Every Reservation has one Passenger as its creator
			all r: Reservation|one p:Passenger|r in p.books

			//Creator of Reservation and related Call Request must be the same
			 all p:Passenger, r:Reservation,c:CallRequest| ( r in p.books and r.call=c) implies p.activeCall=c

			// Departure and arrival place of a Call Request must be the same of the related Reservation
			
		

			//A CallRequest have at most one Reservation
			
			all c:CallRequest | lone  r:Reservation | r.call=c

}

fact CallRequestProperties{
					
				//All CallRequest must have one Passenger and at most one TaxiDriver
					all c:CallRequest | one  r:Passenger | r.activeCall=c
					all c:CallRequest | lone  r:TaxiDriver | r.activeCall=c

}



fact TaxiExceptionProperties{

				//Every TaxiException must have a TaxiDriver  who  raised it
				all e:TaxiException|one t:TaxiDriver|e in t.exceptionRaised 
				
				//If a TaxiException is related to  a CallRequest the TaxiDriver who raised it can't have that Call  as his ActiveCall
				all t:TaxiDriver|all e:TaxiException | all c:CallRequest | ( e.related=c and e in t.exceptionRaised) implies t.activeCall!=c

				//It can't be  more that one exception for one Driver to 
				all t:TaxiDriver,c:CallRequest| lone e:TaxiException | (e.related=c and e in t.exceptionRaised )


}




//Predicates

//pred for assign a CallRequest to a Passenger
pred  addCallRequest	(c:CallRequest,p:Passenger){

							#(p.activeCall)=0 implies p.activeCall=c

}

run addCallRequest  for 4

//pred for cancel ActiveCall of a Passenger
pred  cancelCallRequest	(p:Passenger){
								
				#(p.activeCall)=1 implies p.activeCall=p.activeCall-p.activeCall 

}

run cancelCallRequest  for 5


//pred for assign a CallRequest to a TaxiDriver
pred assignCallRequestToDriver(t:TaxiDriver,c:CallRequest){
		
						 all t1:TaxiDriver|(t1.activeCall!=c or #(t.activeCall)=0 )implies t.activeCall=c
						}
run assignCallRequestToDriver for 5

//pred for reject a CallRequest from a TaxiDriver
pred rejectCallFromDriver(t:TaxiDriver,c:CallRequest){

						all t1:TaxiDriver|(t1.activeCall=c  )  implies t.activeCall=c-c
}
run rejectCallFromDriver for 5





//pred for add a TaxiException to  a TaxiDriver
pred  addTaxiException(t,t':TaxiDriver,e:TaxiException){

							e not in t.exceptionRaised implies t.exceptionRaised=t'.exceptionRaised+e

}

run addTaxiException  for 5

//pred for delete a TaxiException of a  TaxiDriver
pred  deleteTaxiException(t,t':TaxiDriver,e:TaxiException){

							e  in t.exceptionRaised implies t'.exceptionRaised=t.exceptionRaised-e

}

run deleteTaxiException  for 5

pred assignTaxiDriverToZone(z,z':Zone,t:TaxiDriver){

			t not in z.taxiQueue.taxiList implies z'.taxiQueue.taxiList= z.taxiQueue.taxiList+t

}

run assignTaxiDriverToZone  for 5


pred removeTaxiDriverFromZone(z,z':Zone,t:TaxiDriver){

			t  in z.taxiQueue.taxiList implies z'.taxiQueue.taxiList= z.taxiQueue.taxiList-t

}

run assignTaxiDriverToZone  for 5

//--------ASSERT--------//


//no Driver with a ActiveCall in a Queue 
assert noDriverQueueActive{

		all t:TaxiDriver,z:Zone | (#(t.activeCall)=1) implies t not in z.taxiQueue.taxiList

}
check  noDriverQueueActive for 10

//no more than 1 call for a Passenger
assert noMultipleCallForPassenger{

		all p:Passenger|#(p.activeCall)<2

}
check noMultipleCallForPassenger for 7


//to check add and delete TaxiException
assert checkUndoAddTaxiException{

     all t,t',t'':TaxiDriver,e:TaxiException| (e not in t.exceptionRaised and addTaxiException[t,t',e] and deleteTaxiException[t',t'',e]) implies t.exceptionRaised=t''.exceptionRaised
     

}

check  checkUndoAddTaxiException for 6

//check AddCallRequest
assert checkAddCallRequest{

		all p:Passenger,c:CallRequest| (#(p.activeCall)=0 and  addCallRequest[c,p]) implies p.activeCall=c

}

//check AddCancelRequest
assert checkCancelCallRequest{

		all p:Passenger| (#(p.activeCall)=1 and  cancelCallRequest[p]) implies #(p.activeCall)=0

}

check checkCancelCallRequest for 10


//check assignTaxiDriverToZone
assert checkassignTaxiDriverToZone{

				all t:TaxiDriver,z,z':Zone |(t not in  z.taxiQueue.taxiList) and assignTaxiDriverToZone[z,z',t] implies t in z'.taxiQueue.taxiList

}

check checkassignTaxiDriverToZone for 10


//check removeTaxiDriverFromZone
assert checkremoveTaxiDriverFromZone{

				all t:TaxiDriver,z,z':Zone |(t in  z.taxiQueue.taxiList) and removeTaxiDriverFromZone[z,z',t] implies t not in z'.taxiQueue.taxiList

}
check checkremoveTaxiDriverFromZone for 10

//check assignCallRequestToDriver
assert checkrassignCallRequestToDriver{

				all t:TaxiDriver,c:CallRequest |#(t.activeCall)=0 and assignCallRequestToDriver[t,c] implies t.activeCall=c

}
check checkrassignCallRequestToDriver for 10



//check rejectCallFromDriver
assert checkrejectCallFromDriver{

				all t:TaxiDriver,c:CallRequest |t.activeCall=c and rejectCallFromDriver[t,c] implies #(t.activeCall)=0

}
check checkrejectCallFromDriver for 10






//------- PREDICATES--------------------//

pred showPassengerRelation{

			#Passenger=1
			#TaxiDriver=1
			#Reservation=1
			#CallRequest=1
			#RunInfo=1
			#Place=1	
			#Exception=0
			#City=1
			#Zone=1
			
	
}
run showPassengerRelation 




pred show {
	
		#Passenger=8
		#TaxiDriver=6
		#Zone=5
		#CallRequest=6
		#TaxiException=2
}

run show   for 20

