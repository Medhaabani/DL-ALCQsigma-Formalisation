theory All imports CodegenScala Decide_satisfiability 
       ALC_ImplementationProofs ALC_Termination
begin


value "wp_dl (EAdd x r y) (QFactFm (AtomR True r (Free x) (Free y)))"

definition "push_subst f = push_subst_form (form_of_qform f) []"

value "push_subst (wp_dl (EAdd x r y) (QFactFm (AtomR True r (Free x) (Free y))))"

end
