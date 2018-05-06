/***** Various datatypes *****/
datatype MOTOR = ON | OFF
datatype DOOR = OPEN | HALF | CLOSED
datatype SHAFT = UP | DOWN

/*
 * Class for Cabins
 */
class CABIN {

    var floor: int;    // The current cabin's floor
    var motor: MOTOR;  // The current status of the cabin's motor
    var door: DOOR;    // The current status of the cabin's door
    var shaft: SHAFT;  // The current shaft of the cabin
    var floor_buttons_array: array<bool> // The current status of the floor requests (from within the cabin)

    /*
     * Method for setting the floor of the cabin.
     */
    method SetFloor(floor : int)
        modifies this;
        ensures this.floor == floor;
    {
        this.floor := floor;
    }

    /*
     * Method for setting the motor status of the cabin.
     */
    method SetMotor(motor : MOTOR)
        modifies this;
        ensures floor == old(floor);
        ensures this.motor == motor;
        ensures door == old(door);
        ensures shaft == old(shaft);
        ensures floor_buttons_array == old(floor_buttons_array);
    {
        this.motor := motor;
    }

    /*
     * Method for setting the door status of the cabin.
     */
    method SetDoor(door : DOOR)
        modifies this;
        ensures this.door == door
    {
	this.door := door;
    }

    /*
     * Method for setting the shaft of the cabin.
     */
    method SetShaft(shaft : SHAFT)
        modifies this;
        ensures this.shaft == shaft;
    {
      	this.shaft := shaft;
    }

    /*
     * Method for setting the particular floor button of the cabin.
     */
    method SetFloorButton(floor : int, b : bool)
        requires 0 <= floor
        requires floor_buttons_array != null
        requires floor < floor_buttons_array.Length
        modifies floor_buttons_array;
        ensures floor_buttons_array[floor] == b;
    {
      	floor_buttons_array[floor] := b;
    }

}

/*
 * Main class for MULTI elevator system
 */
class MULTI {

    /***** Constants *****/
    var MAX_FLOOR: int;			// The number of floors.
    var MAX_CABIN: int;			// The number of cabins.
    var cabins_array: array<CABIN>;     // The array of cabins

    /***** Axioms *****/
    predicate Axioms()
        reads this
    	reads cabins_array
    {
	AxiomsPred(MAX_FLOOR, MAX_CABIN, cabins_array)
    }

    // Helper predicate for defining Axioms and the precondition of method Init()
    predicate AxiomsPred(MAX_FLOOR : int, MAX_CABIN : int, cabins_array : array<CABIN>)
        reads this
    	reads cabins_array
    {
	0 < MAX_FLOOR && // There are positive number of floors
	0 < MAX_CABIN && // There are positive number of cabins
	cabins_array != null && // The cabins array is none null
	cabins_array.Length == MAX_CABIN && // There are MAX_CABIN cabins.
	(forall i :: 0 <= i < MAX_CABIN ==> cabins_array[i] != null) // Each cabin in the array is also none null.
    }


    /***** Variables *****/
    var up_buttons_array: array<bool>;	// The array of up buttons
    var down_buttons_array: array<bool>; // The array of down buttons

    /***** Invariants *****/
    predicate Invariants()
        requires Axioms()
    	reads this
	reads cabins_array
  	reads (set i | 0 <= i < cabins_array.Length :: cabins_array[i])
    	reads up_buttons_array
    	reads down_buttons_array
    {
	(
	forall i :: 0 <= i < MAX_CABIN ==>
	       0 <= cabins_array[i].floor < MAX_FLOOR &&
	       (cabins_array[i].motor == ON || cabins_array[i].motor == OFF) &&
	       (cabins_array[i].shaft == UP || cabins_array[i].shaft == DOWN) &&
	       cabins_array[i].floor_buttons_array != null &&
	       cabins_array[i].floor_buttons_array.Length == MAX_FLOOR
	) &&
	up_buttons_array != null && // The up buttons array is none null
	up_buttons_array.Length == MAX_FLOOR && // There are MAX_FLOOR number of up buttons (we will ignore the last one)
	down_buttons_array != null && // The down buttons array is none null
	down_buttons_array.Length == MAX_FLOOR // There are MAX_FLOOR number of down buttons (we will ignore the firs one)
    }

    /*
     * This predicate specifies that a cabin c must stop at the current floor while going up
     * One of the following condition hold
     * - there is a floor request from the cabin for the current floor.
     * - there is an up request from the current floor.
     * - If the current floor is the top floor.
     * - if the current floor is not a top floor, and there is a cabin on the floor above.
     */
    predicate MustStopGoingUpPred(c : CABIN)
	requires Axioms()
	requires Invariants()
	requires c != null
	requires (exists i :: 0 <= i < MAX_CABIN && cabins_array[i] == c)
    	reads this
	reads cabins_array
  	reads (set i | 0 <= i < cabins_array.Length :: cabins_array[i])
  	reads c.floor_buttons_array
    	reads up_buttons_array
    	reads down_buttons_array
	reads c
    {
        // FIXME (B1): Specify the body of this predicate
        c.floor_buttons_array[c.floor] ||
        up_buttons_array[c.floor] ||
        (c.floor == MAX_FLOOR) ||
        ((c.floor != MAX_FLOOR) && (cabins_array[cabins_array.Length-1] != c))
    }

    /*
     * Method for checking if a cabin c must stop at the current floor.
     */
    method MustStopGoingUp(c : CABIN) returns (b: bool)
	requires Axioms()
	requires Invariants()
	requires c != null
	requires (exists i :: 0 <= i < MAX_CABIN && cabins_array[i] == c)

	ensures Axioms()
	ensures Invariants()
        ensures b == old(MustStopGoingUpPred(c))
	ensures (exists i :: 0 <= i < MAX_CABIN && cabins_array[i] == c)
    {
	// FIXME (B2): Implement the body of this method
	return true;
    }

    /*
     * This predicate specifies that a cabin c must stop at the current floor while going down
     * The body of this predicate is INTENTIONALLY left out.
     */
    predicate MustStopGoingDownPred(c : CABIN)
	requires Axioms()
	requires Invariants()
	requires c != null
	requires (exists i :: 0 <= i < MAX_CABIN && cabins_array[i] == c)
    	reads this
	reads cabins_array
  	reads (set i | 0 <= i < cabins_array.Length :: cabins_array[i])
  	reads c.floor_buttons_array
    	reads up_buttons_array
    	reads down_buttons_array
	reads c

    /*
     * Method for checking if a cabin c must stop at the current floor.
     * The body of this method is INTENTIONALLY left out.
     */
    method MustStopGoingDown(c : CABIN) returns (b: bool)
	requires Axioms()
	requires Invariants()
	requires c != null
	requires (exists i :: 0 <= i < MAX_CABIN && cabins_array[i] == c)
	ensures Axioms()
	ensures Invariants()
        ensures b == old(MustStopGoingDownPred(c))
	ensures (exists i :: 0 <= i < MAX_CABIN && cabins_array[i] == c)

    /*
     * Method to stop the cabin's motor while going up.
     */
    method MotorStopsGoingUp(c: CABIN)
	requires Axioms()
	requires Invariants()
	requires c != null
	requires c.motor == ON
	requires c.shaft == UP
	requires (exists i :: 0 <= i < MAX_CABIN && cabins_array[i] == c)
	requires MustStopGoingUpPred(c)
	ensures Axioms()
	ensures Invariants()
        ensures c.motor == OFF
	modifies c
    {
	c.SetMotor(OFF);
    }

    /*
     * Method to start the cabin's motor while going up.
     */
    method MotorStartsGoingUp(c: CABIN)
	requires Axioms()
	requires Invariants()
	requires c != null
	requires c.motor == OFF
	requires c.shaft == UP
	requires (exists i :: 0 <= i < MAX_CABIN && cabins_array[i] == c)
	requires !MustStopGoingUpPred(c)
	ensures Axioms()
	ensures Invariants()
        ensures c.motor == ON
	modifies c
    {
	c.SetMotor(ON);
    }

    /*
     * Method to stop the cabin's motor while going down
     */
    method MotorStopsGoingDown(c: CABIN)
	requires Axioms()
	requires Invariants()
	requires c != null
	requires c.motor == ON
	requires c.shaft == DOWN
	requires (exists i :: 0 <= i < MAX_CABIN && cabins_array[i] == c)
	requires MustStopGoingDownPred(c)
	ensures Axioms()
	ensures Invariants()
        ensures c.motor == OFF
	modifies c
    {
	c.SetMotor(OFF);
    }

    /*
     * Method to start the cabin's motor while going down.
     */
    method MotorStartsGoingDown(c: CABIN)
	requires Axioms()
	requires Invariants()
	requires c != null
	requires c.motor == OFF
	requires c.shaft == DOWN
	requires (exists i :: 0 <= i < MAX_CABIN && cabins_array[i] == c)
	requires !MustStopGoingDownPred(c)
	ensures Axioms()
	ensures Invariants()
        ensures c.motor == ON
	modifies c
    {
	c.SetMotor(ON);
    }

    /*
     * Main method for control a cabin's motor. 
     */
    method ControlMotor(c : CABIN)
        requires Axioms()
        requires Invariants()
        ensures Axioms()
        ensures Invariants()
	requires c != null
	requires (exists i :: 0 <= i < MAX_CABIN && cabins_array[i] == c)
	modifies c
    {
        // FIXME (B3): Implement the body of this method. You must make a call to MotorStartsGoingUp, MotorStopsGoingUp, MotorStartsGoingDown, MotorStopsGoingDown to control the cabin's motor accordingly.	    
    }

    /*
     * Method for controlling the motors of all cabins.
     */
    method MotorController()
        requires Axioms()
        requires Invariants()
        ensures Axioms()
        ensures Invariants()
        modifies (set i | 0 <= i < cabins_array.Length :: cabins_array[i])
    {
        // FIXME (B4): Implement the body of this method for controlling the movement of ALL cabins. Hint: Use ControlMotor method.
    }

}




