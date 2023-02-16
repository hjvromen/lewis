# lewis
This repository contains formalisations of Lewis' theory of common knowledge as presented in his book Convention: A Philosophical Study. Cambridge, MA: Harvard University Press, 1969.

First, the formalisation of Cubitt and Sugden is presented and formally verified. 
file : cubitt_sugden.lean

Second, the formalisation of Sillari is discussed. He uses a Kripke semantics. Therefore I start with an embedding of modal logic in Lean. After that I present a multi-agent modal logic. Then follows the discussion of Sillari's theory. It turns out that his account contains contradictions and that his proof of Lewis' theorem is unsound.
files : modal_logic.lean, modal_logic_multi_agent.lean, sillari.lean

Third, I present my own - not yet published - formalisation.
file : reasons.lean



Bibliography

Artemov, Sergei, and Melvin Fitting. Justification Logic - Reasoning with Reasons. Cambridge: Cambridge University Press, 2019.

Cubitt, Robin P., and Robert Sugden. ‘Common Knowledge, Salience and Convention: A Reconstruction of David Lewis’ Game Theory’. Economics and Philosophy 19 (2003): 175–210.

Fagin, Ronald, Joseph Y. Halpern, Yoram Moses, and Moshe Y. Vardi. Reasoning about Knowledge. Cambridge, MA: MIT Press, 1995.

Gamut, L T F. ‘Logic, Language and Meaning Volume 2’. Chicago: University of Chicago Press, 1991.

Garson, James W. Modal Logic for Philosophers. 2nd ed. Cambridge: Cambridge University Press, 2013.

Lewis, David. Convention: A Philosophical Study. Cambridge, MA: Harvard University Press, 1969.

Pacuit, Eric. Neighborhood Semantics for Modal Logic. Short Textbooks in Logic. Cham: Springer International Publishing, 2017.

Sillari, Giacomo. ‘A Logical Framework for Convention’. Synthese 147, no. 2 (November 2005): 379–400. https://doi.org/10.1007/s11229-005-1352-z.

Uckelman, Sara L. ‘What Is Logic?’ Durham, 5 February 2021.
