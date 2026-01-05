/* Battleship Game
 * Author: Asal Samarasinghe
 * Creation date: 12/29/2025
 */
MACHINE
    BattleshipGame

SETS
    PLAYERS = {player1, player2};
    REPORT = {P1_SUBMARINE_DEPLOYED, P1_DESTROYER_DEPLOYED, P1_CRUISER_DEPLOYED, P2_SUBMARINE_DEPLOYED, P2_DESTROYER_DEPLOYED, P2_CRUISER_DEPLOYED,
              ALREADY_DEPLOYED, INVALID_LOCATION_TRY_AGAIN, HIT, MISS, P1_SUBMARINE_SUNK, P1_DESTROYER_SUNK, P1_CRUISER_SUNK, P2_SUBMARINE_SUNK,
              P2_DESTROYER_SUNK, P2_CRUISER_SUNK, PLAYER_1_WON, PLAYER_2_WON, GAME_ONGOING, SETTING_UP_SHIPS, ALREADY_SHOT};
    GAME_STATUS = {setting_up_sub, setting_up_dest, setting_up_cruis, playing, player_1_win, player_2_win};
    ORIENTATION = {horizontal, vertical}
    
DEFINITIONS
    ANIMATION_FUNCTION  == ({ row, col, img | col:(1..(GRID_SIZE*2)+1) & row:(1..GRID_SIZE) & img=1 });
    ANIMATION_FUNCTION1 == ({ row, col, img | col:(1..(GRID_SIZE*2)+1) & row:(1..GRID_SIZE) & img=2 & col = 11 });
    ANIMATION_FUNCTION2 == ({ row, col, img | col:(1..(GRID_SIZE*2)+1) & row:(1..GRID_SIZE) & img=3 & (col,11-row) : p1_sub });
    ANIMATION_FUNCTION3 == ({ row, col, img | col:(1..(GRID_SIZE*2)+1) & row:(1..GRID_SIZE) & img=4 & (col-11,11-row) : p2_sub });
    ANIMATION_FUNCTION4 == ({ row, col, img | col:(1..(GRID_SIZE*2)+1) & row:(1..GRID_SIZE) & img=5 & (col,11-row) : p1_dest });
    ANIMATION_FUNCTION5 == ({ row, col, img | col:(1..(GRID_SIZE*2)+1) & row:(1..GRID_SIZE) & img=6 & (col-11,11-row) : p2_dest });
    ANIMATION_FUNCTION6 == ({ row, col, img | col:(1..(GRID_SIZE*2)+1) & row:(1..GRID_SIZE) & img=7 & (col,11-row) : p1_cruis });
    ANIMATION_FUNCTION7 == ({ row, col, img | col:(1..(GRID_SIZE*2)+1) & row:(1..GRID_SIZE) & img=8 & (col-11,11-row) : p2_cruis });
    ANIMATION_FUNCTION8 == ({ row, col, img | col:(1..(GRID_SIZE*2)+1) & row:(1..GRID_SIZE) & img=9 & (col,11-row) : p1_hits });
    ANIMATION_FUNCTION9 == ({ row, col, img | col:(1..(GRID_SIZE*2)+1) & row:(1..GRID_SIZE) & img=9 & (col-11,11-row) : p2_hits });
    ANIMATION_FUNCTION10 == ({ row, col, img | col:(1..(GRID_SIZE*2)+1) & row:(1..GRID_SIZE) & img=10 & (col,11-row) : p1_misses });
    ANIMATION_FUNCTION11 == ({ row, col, img | col:(1..(GRID_SIZE*2)+1) & row:(1..GRID_SIZE) & img=10 & (col-11,11-row) : p2_misses });
    

/* Images for animations */
    ANIMATION_IMG1 == "images/sea.png";
    ANIMATION_IMG2 == "images/breaker.png";  
    ANIMATION_IMG3 == "images/submarine.png";
    ANIMATION_IMG4 == "images/submarine_p2.png";
    ANIMATION_IMG5 == "images/destroyer.png";
    ANIMATION_IMG6 == "images/destroyer_p2.png";
    ANIMATION_IMG7 == "images/cruiser.png";
    ANIMATION_IMG8 == "images/cruiser_p2.png";
    ANIMATION_IMG9 == "images/hit.png";
    ANIMATION_IMG10 == "images/miss.png";

CONSTANTS
    GRID_SIZE, GRID, SUB_SIZE, DEST_SIZE, CRUIS_SIZE
    
PROPERTIES
    GRID_SIZE = 10 &
    SUB_SIZE = 1 &
    DEST_SIZE = 2 &
    CRUIS_SIZE = 3 &
    GRID = (1..GRID_SIZE) * (1..GRID_SIZE)

VARIABLES
    p1_sub, p1_dest, p1_cruis, p1_ships,
    p2_sub, p2_dest, p2_cruis, p2_ships,
    current_player,
    game_state,
    p1_shots,
    p2_shots,
    p1_hits,
    p2_hits,
    p1_misses,
    p2_misses,
    p1_ships_count,
    p2_ships_count

INVARIANT
    p1_sub <: GRID & card(p1_sub) <= SUB_SIZE &
    p1_dest <: GRID & card(p1_dest) <= DEST_SIZE &
    p1_cruis <: GRID & card(p1_cruis) <= CRUIS_SIZE &
    p1_sub /\ p1_dest = {} &
    p1_sub /\ p1_cruis = {} &
    p1_dest /\ p1_cruis = {} &
    
    p2_sub <: GRID & card(p2_sub) <= SUB_SIZE &
    p2_dest <: GRID & card(p2_dest) <= DEST_SIZE &
    p2_cruis <: GRID & card(p2_cruis) <= CRUIS_SIZE &
    p2_sub /\ p2_dest = {} &
    p2_sub /\ p2_cruis = {} &
    p2_dest /\ p2_cruis = {} &
    
    p1_ships = p1_sub \/ p1_dest \/ p1_cruis &
    p2_ships = p2_sub \/ p2_dest \/ p2_cruis &
    current_player : PLAYERS &
    game_state : GAME_STATUS &
    p1_shots : NAT & 
    p2_shots : NAT &
    p1_hits <: GRID &
    p2_hits <: GRID &
    p1_misses <: GRID &
    p2_misses <: GRID &
    p1_ships_count : NAT &
    p2_ships_count : NAT

INITIALISATION
    p1_sub, p1_dest, p1_cruis := {}, {}, {} ||
    p2_sub, p2_dest, p2_cruis := {}, {}, {} ||
    p1_ships := {} || p2_ships := {} ||
    
    current_player := player1 ||
    game_state := setting_up_sub ||
    p1_shots := 0 ||
    p2_shots := 0 ||
    p1_hits := {} ||
    p2_hits := {} ||
    p1_misses := {} ||
    p2_misses := {} ||
    p1_ships_count := 0 ||
    p2_ships_count := 0

OPERATIONS
    /* Setting up the Submarine */
    report <-- DeploySubmarine( player, position ) =
    PRE
        player : PLAYERS &
        current_player = player &
        position : GRID &
        game_state = setting_up_sub & 
        report : REPORT
    THEN
        IF card(p1_sub) = SUB_SIZE & card(p2_sub) = SUB_SIZE
        THEN
            game_state := setting_up_dest
        ELSE
            IF player = player1 THEN
                IF p1_sub = {} THEN
                    p1_sub := {position} ||
                    p1_ships := p1_ships \/ {position} ||
                    report := P1_SUBMARINE_DEPLOYED ||
                    p1_ships_count := p1_ships_count + 1 ||
                    current_player := player2
                ELSE
                    report := ALREADY_DEPLOYED
                END
            ELSE
                IF p2_sub = {} THEN
                    p2_sub := {position} ||
                    p2_ships := p2_ships \/ {position} ||
                    report := P2_SUBMARINE_DEPLOYED ||
                    p2_ships_count := p2_ships_count + 1 ||
                    current_player := player1 ||
                    game_state := setting_up_dest
                ELSE
                    report := ALREADY_DEPLOYED
                END
            END
        END
    END;

    /* Setting up the Destroyer */
    report <-- DeployDestroyer( player, position, orientation ) =
    PRE
        player : PLAYERS & 
        current_player = player & 
        orientation : ORIENTATION &
        position : GRID &
        game_state = setting_up_dest & 
        report : REPORT &
        ((player = player1 & p1_sub /= {} & p1_dest = {}) or 
        (player = player2 & p2_sub /= {} & p2_dest = {}))
    THEN
        IF card(p1_dest) = DEST_SIZE & card(p2_dest) = DEST_SIZE
        THEN
            game_state := setting_up_cruis
        ELSE   
            IF player = player1 THEN
                IF orientation = horizontal THEN
                    IF prj1(position) + 1 <= GRID_SIZE & ({position, (prj1(position) + 1 |-> prj2(position))} /\ p1_ships = {}) THEN
                        p1_dest := {position, (prj1(position) + 1 |-> prj2(position))} ||
                        p1_ships := p1_ships \/ {position, (prj1(position) + 1 |-> prj2(position))} ||
                        report := P1_DESTROYER_DEPLOYED ||
                        p1_ships_count := p1_ships_count + 1 ||
                        current_player := player2
                    ELSE
                        report := INVALID_LOCATION_TRY_AGAIN
                    END
                ELSE
                    IF ({position, (prj1(position) |-> prj2(position) - 1)} <: GRID) & ({position, (prj1(position) |-> prj2(position) - 1)} /\ p1_ships = {}) THEN
                        p1_dest := {position, (prj1(position) |-> prj2(position) - 1)} ||
                        p1_ships := p1_ships \/ {position, (prj1(position) |-> prj2(position) - 1)} ||
                        report := P1_DESTROYER_DEPLOYED ||
                        p1_ships_count := p1_ships_count + 1 ||
                        current_player := player2
                    ELSE
                        report := INVALID_LOCATION_TRY_AGAIN
                    END
                END 
            ELSE
                IF orientation = horizontal THEN
                    IF prj1(position) + 1 <= GRID_SIZE & ({position, (prj1(position) + 1 |-> prj2(position))} /\ p2_ships = {}) THEN
                        p2_dest := {position, (prj1(position) + 1 |-> prj2(position))} ||
                        p2_ships := p2_ships \/ {position, (prj1(position) + 1 |-> prj2(position))} ||
                        report := P2_DESTROYER_DEPLOYED ||
                        p2_ships_count := p2_ships_count + 1 ||
                        current_player := player1 ||
                        game_state := setting_up_cruis
                    ELSE
                        report := INVALID_LOCATION_TRY_AGAIN
                    END
                ELSE
                    IF ({position, (prj1(position) |-> prj2(position) - 1)} <: GRID) & ({position, (prj1(position) |-> prj2(position) - 1)} /\ p2_ships = {}) THEN
                        p2_dest := {position, (prj1(position) |-> prj2(position) - 1)} ||
                        p2_ships := p2_ships \/ {position, (prj1(position) |-> prj2(position) - 1)} ||
                        report := P2_DESTROYER_DEPLOYED ||
                        p2_ships_count := p2_ships_count + 1 ||
                        current_player := player1 ||
                        game_state := setting_up_cruis
                    ELSE
                        report := INVALID_LOCATION_TRY_AGAIN
                    END
                END 
            END
        END
    END;
   
   /* Setting up the Cruiser */
    report <-- DeployCruiser( player, position, orientation ) =
    PRE
        player : PLAYERS & 
        current_player = player & 
        orientation : ORIENTATION &
        position : GRID &
        game_state = setting_up_cruis & 
        report : REPORT &
        ((player = player1 & p1_sub /= {} & p1_dest /= {} & p1_cruis ={}) or 
        (player = player2 & p2_sub /= {} & p2_dest /= {} & p2_cruis ={}))
    THEN
        IF card(p1_cruis) = CRUIS_SIZE & card(p2_cruis) = CRUIS_SIZE
        THEN
            game_state := playing
        ELSE   
            IF player = player1 THEN
                IF orientation = horizontal THEN
                    IF prj1(position) + 2 <= GRID_SIZE &
                        ({position, (prj1(position) + 1 |-> prj2(position)), (prj1(position) + 2 |-> prj2(position))} /\ p1_ships = {})
                    THEN
                        p1_cruis := {position, (prj1(position) + 1 |-> prj2(position)), (prj1(position) + 2 |-> prj2(position))} ||
                        p1_ships := p1_ships \/ {position, (prj1(position) + 1 |-> prj2(position)), (prj1(position) + 2 |-> prj2(position))} ||
                        report := P1_CRUISER_DEPLOYED ||
                        p1_ships_count := p1_ships_count + 1 ||
                        current_player := player2
                    ELSE
                        report := INVALID_LOCATION_TRY_AGAIN
                    END
                ELSE
                    IF ({position, (prj1(position) |-> prj2(position) - 1), (prj1(position) |-> prj2(position) - 2)} <: GRID) &
                        ({position, (prj1(position) |-> prj2(position) - 1), (prj1(position) |-> prj2(position) - 2)} /\ p1_ships = {}) 
                    THEN
                        p1_cruis := {position, (prj1(position) |-> prj2(position) - 1), (prj1(position) |-> prj2(position) - 2)} ||
                        p1_ships := p1_ships \/ {position, (prj1(position) |-> prj2(position) - 1), (prj1(position) |-> prj2(position) - 2)} ||
                        report := P1_CRUISER_DEPLOYED ||
                        p1_ships_count := p1_ships_count + 1 ||
                        current_player := player2
                    ELSE
                        report := INVALID_LOCATION_TRY_AGAIN
                    END
                END 
            ELSE
                IF orientation = horizontal THEN
                    IF prj1(position) + 2 <= GRID_SIZE &
                        ({position, (prj1(position) + 1 |-> prj2(position)), (prj1(position) + 2 |-> prj2(position))} /\ p2_ships = {})
                    THEN
                        p2_cruis := {position, (prj1(position) + 1 |-> prj2(position)), (prj1(position) + 2 |-> prj2(position))} ||
                        p2_ships := p2_ships \/ {position, (prj1(position) + 1 |-> prj2(position)), (prj1(position) + 2 |-> prj2(position))} ||
                        report := P2_CRUISER_DEPLOYED ||
                        p2_ships_count := p2_ships_count + 1 ||
                        current_player := player1 ||
                        game_state := playing
                    ELSE
                        report := INVALID_LOCATION_TRY_AGAIN
                    END
                ELSE
                    IF ({position, (prj1(position) |-> prj2(position) - 1), (prj1(position) |-> prj2(position) - 2)} <: GRID) &
                        ({position, (prj1(position) |-> prj2(position) - 1), (prj1(position) |-> prj2(position) - 2)} /\ p2_ships = {}) 
                    THEN
                        p2_cruis := {position, (prj1(position) |-> prj2(position) - 1), (prj1(position) |-> prj2(position) - 2)} ||
                        p2_ships := p2_ships \/ {position, (prj1(position) |-> prj2(position) - 1), (prj1(position) |-> prj2(position) - 2)} ||
                        report := P2_CRUISER_DEPLOYED ||
                        p2_ships_count := p2_ships_count + 1 ||
                        current_player := player1 ||
                        game_state := playing
                    ELSE
                        report := INVALID_LOCATION_TRY_AGAIN
                    END
                END
            END
        END
    END;
   

    /* Player Shoots Operation */
    report <-- Shoot( player, target) =
    PRE
        player : PLAYERS &
        current_player = player & 
        target : GRID &
        game_state = playing &
        report : REPORT &
        ((player = player1 & p1_sub /= {} & p1_dest /= {} & p1_cruis /= {}) or /*Optional validation*/
        (player = player2 & p2_sub /= {} & p2_dest /= {} & p2_cruis /= {}))
    THEN
        IF player = player1 THEN
            p1_shots := p1_shots + 1 ||
            p2_hits := p2_hits \/ {target}||
            IF target : p2_ships THEN
                p2_ships := p2_ships - {target} ||
                IF p2_ships - {target} = {} THEN
                    p2_ships_count := p2_ships_count - 1 ||
                    game_state := player_1_win ||
                    report := PLAYER_1_WON
                ELSE
                    IF {target} = p2_sub THEN
                        p2_ships_count := p2_ships_count - 1 ||
                        report := P2_SUBMARINE_SUNK
                    ELSIF target : p2_dest THEN
                        IF p2_dest - {target} = {} THEN
                            p2_ships_count := p2_ships_count - 1 ||
                            report := P2_DESTROYER_SUNK
                        ELSE
                            p2_dest := p2_dest - {target} ||
                            report := HIT
                        END
                    ELSE
                        IF p2_cruis - {target} = {} THEN
                            p2_ships_count := p2_ships_count - 1 ||
                            report := P2_CRUISER_SUNK
                        ELSE
                            p2_cruis := p2_cruis - {target} ||
                            report := HIT
                        END
                    END ||
                    current_player := player2
                END
            ELSIF (target : p2_hits) THEN
                report := ALREADY_SHOT
            ELSE
                report := MISS ||
                p2_misses := p2_misses \/ {target}||
                current_player := player2
            END
        ELSE
            p2_shots := p2_shots + 1 ||
            p1_hits :=  p1_hits \/ {target}||
            IF target : p1_ships THEN
                p1_ships := p1_ships - {target} ||
                IF p1_ships - {target} = {} THEN
                    p1_ships_count := p1_ships_count - 1 ||
                    game_state := player_2_win ||
                    report := PLAYER_2_WON
                ELSE
                    IF {target} = p1_sub THEN
                        p1_ships_count := p1_ships_count - 1 ||
                        report := P1_SUBMARINE_SUNK
                    ELSIF target : p1_dest THEN
                        IF p1_dest - {target} = {} THEN
                            p1_ships_count := p1_ships_count - 1 ||
                            report := P1_DESTROYER_SUNK
                        ELSE
                            p1_dest := p1_dest - {target} ||
                            report := HIT
                        END
                    ELSE
                        IF p1_cruis - {target} = {} THEN
                            p1_ships_count := p1_ships_count - 1 ||
                            report := P1_CRUISER_SUNK
                        ELSE
                            p1_cruis := p1_cruis - {target} ||
                            report := HIT
                        END
                    END ||
                    current_player := player1
                END
            ELSIF (target : p1_hits) THEN
                report := ALREADY_SHOT
            ELSE
                report := MISS ||
                p1_misses := p1_misses \/ {target}||
                current_player := player1
            END
        END
    END;

    /* Ships Location Operation */
    shipSquares <-- LocationOfShips( player ) =
    PRE
        player : PLAYERS
        
    THEN
        IF player = player1 THEN
            shipSquares := p1_ships
        ELSE
            shipSquares := p2_ships
        END
    END;

    /* Ships count operation */
    shipsCount <-- ShipsLeft( player ) =
    PRE
        player : PLAYERS
    THEN
        IF player = player1 THEN
            shipsCount := p1_ships_count
        ELSE
            shipsCount := p2_ships_count
        END 
    END;

    /* Taken shots count operation */
    shotCount <-- ShotsTaken( player ) = 
    PRE
        player : PLAYERS
    THEN
        IF player = player1 THEN
            shotCount := p1_shots
        ELSE
            shotCount := p2_shots
        END
    END;
    
    /* Game status operation */
    report <-- GameState =
    BEGIN
        IF game_state = setting_up_sub or
            game_state = setting_up_dest or
            game_state = setting_up_cruis
        THEN
            report := SETTING_UP_SHIPS
        ELSIF game_state = playing THEN
            report := GAME_ONGOING
        ELSIF game_state = player_1_win THEN
            report := PLAYER_1_WON
        ELSIF game_state = player_2_win THEN
            report := PLAYER_2_WON
        ELSE
            report := GAME_ONGOING
        END
    END;

    /* Restarting game operation */
    restartGame = 
    BEGIN
        p1_sub, p1_dest, p1_cruis := {}, {}, {} ||
        p2_sub, p2_dest, p2_cruis := {}, {}, {} ||
        p1_ships := {} || p2_ships := {} ||
        
        current_player := player1 ||
        game_state := setting_up_sub ||
        p1_shots := 0 ||
        p2_shots := 0 ||
        p1_hits := {} ||
        p2_hits := {} ||
        p1_misses := {} ||
        p2_misses := {} ||
        p1_ships_count := 0 ||
        p2_ships_count := 0
    END

END
