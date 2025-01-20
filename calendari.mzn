include "globals.mzn";

int: nmachesperday;
int: nmatchesperstadium;
int: ndays;
int: nteams;
int: nstadiums;

set of 1..ndays: days = 1..ndays;
set of 1..nstadiums: stadiums = 1..nstadiums;
set of 1..nteams: teams = 1..nteams;
set of 1..nmachesperday: matchesperday = 1..nmachesperday;

array[days, stadiums] of set of teams: fixes;
array[stadiums, stadiums] of int: distancies;
array[teams] of int: tifosi;
array[stadiums] of int: capacitats;

array[days, stadiums] of var set of teams: schedule;

constraint forall(d in days, s in stadiums)( % Limitem que el set pugui contenir només dos valors
  count(t in fixes[d, s])(t >= 0) <= 2 /\ (count(t in schedule[d, s])(t >= 0) == 2 \/ count(t in schedule[d, s])(t >= 0) == 0)
);

constraint forall(d in days, s in stadiums)( % Inicialitzem schedule amb fixes
  schedule[d, s] union fixes[d, s] == schedule[d, s]
);

constraint forall(d1 in days, s1 in stadiums)( % Els equips només jugaran entre si una vegada
  forall(d2 in days, s2 in stadiums)(
    (d1 == d2 /\ s1 == s2) \/ schedule[d1, s1] == {} \/ schedule[d1, s1] != schedule[d2, s2]
  )
);

array[teams, days] of var stadiums: place;

constraint forall(d in days, s in stadiums)( % Cada equip juga com a molt un cop al dia
  forall(t in schedule[d, s])(
    place[t, d] == s
  )
);

constraint forall(t in teams)( % Cada equip juga un sol cop a cadascun dels estadis
  all_different([place[t, d] | d in days])
);

array[teams] of var int: travelled_distances = [sum([distancies[d, d - 1] | d in 2..ndays]) | t in teams];
var int: total_km = sum(travelled_distances);

% Només trobar una solució correcta
solve satisfy;

% Minimitzar per tots els quilòmetres recorreguts per l'equip
%solve minimize total_km;

% Maximitzar el nombre d'espectadors
%solve maximize sum([max(sum([tifosi[t] | t in schedule[d, s]]), capacitats[s]) | d in days, s in stadiums]);

% Minimitzar quilòmetres i després maximitzar espectadors
%solve minimize total_km + 1 / (sum([max(sum([tifosi[t] | t in schedule[d, s]]), capacitats[s]) | d in days, s in stadiums]));

% Maximitzar espectadors i després minimitzar quilòmetres
%solve maximize sum([max(sum([tifosi[t] | t in schedule[d, s]]), capacitats[s]) | d in days, s in stadiums]) - total_km;

output [
  "     : " ++ concat([ "Es \(s) | " | s in stadiums]),
  "\n------" ++ concat(["-------" | s in stadiums]),
  "\n" ++
  concat([
    "Dia \(d): " ++ concat([
      let { array[int] of var opt int: match = [t | t in schedule[d, s]] }
      in if length(match) > 0 then
        " \(match[1])-\(match[2])"
        else
          "    "
        endif ++
      (if s != nstadiums then " | " else " |\n" endif)
      | s in stadiums
    ])
    | d in days
  ]),
  "------" ++ concat(["-------" | s in stadiums])
];