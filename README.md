# Propositional-Logic-in-Agda

Commity

- Z dużej litery
- Po polsku
- bezosobowo

## Wstęp

Celem tego projektu jest formalizacja logiki klasycznego rachunku zdań oraz udowownienie twierdzenia o zupełności. Twierdzenie to można nieformalnie zapisać jako:

#### Zgodność

Jeśli formuła zdaniowa ma dowód wyprowadzony z danych przesłanek, to wszystkie wartościowania przesłanek, które sprawiają, że są prawdziwe, sprawiają również, że dana formuła jest prawdziwa.

#### Pełność

Jeśli dla każdego wartościowania, dla którego aksiomaty i przesłanki są prawdziwe fromuła zdaniowa również jest prawdziwa, to zawsze jest możliwe skonstruowanie dowodu tej formuły poprzez zastosowanie zasad wnioskowania na danych przesłankach.

Twierdzenie o zupełności składa się z obu powyższych twierdzeń.

## Twierdzenie o zupełności

W tej sekcji podamy definicje potrzebne do zrozumienia problemu oraz dowodu twierdzenia o zupełności

#### Definicja 1

Sekwencją nazywamy zbiór formuł $\phi_1,\phi_2,\dots,\phi_n$, nazywanych przesłankami oraz formułę $\psi$ nazywaną wnioskiem.

#### Definicja 2

Drzewem dowodowym sekwencji $\phi_1,\phi_2,\dots,\phi_n\vdash\psi$ nazywamy drzewo o korzeniu $\psi$, gdzie wszystkie węzły są zasadami wnioskowania w logice rachunku zdań oraz $\phi_1,\phi_2,\dots,\phi_n$ mogą być liśćmi.

#### Definicja 3

Kontekstem nazywamy zbiór wszystkich przesłanek w sekwencji. Sekwencja $\phi_1,\phi_2,\dots,\phi_n\vdash\psi$ może zostać zapisana jako $\Gamma\vdash\psi$, gdzie $\Gamma$ zawiera $\phi_i$ dla wszystkich $i\in\{1,\dots,n\}$. Kiedy sekwencja składa się jedynie z twierdzenia jako wniosku, kontekst jest zbiorem pustym, $\varnothing\vdash\psi$.
