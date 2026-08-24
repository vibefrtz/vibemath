/-
AxiomAudit.lean — run `lake env lean AxiomAudit.lean` to print, for each of
the paper's theorems, the complete list of axioms its proof depends on.
Expected: only Lean's three built-in axioms (propext, Classical.choice,
Quot.sound) and the EKRev.* axioms of `EKRev/Cited.lean`.
-/
import EKRev

open EKRev

#print axioms pal_EK_omega
#print axioms pal_EK_Omega
#print axioms pal_EK_omega_uniform
#print axioms pal_EK_Omega_uniform
#print axioms pal_EK_omegaS
#print axioms pal_EK_OmegaS
#print axioms pal_EK_omegaS_uniform
#print axioms pal_EK_OmegaS_uniform
#print axioms pal_moments
#print axioms rev_EK_omega
#print axioms rev_EK_Omega
#print axioms rev_EK_omega_uniform
#print axioms rev_EK_Omega_uniform
#print axioms rev_EK_omega_loc
#print axioms rev_EK_Omega_loc
#print axioms rev_EK_omegaS_loc
#print axioms rev_EK_OmegaS_loc
#print axioms rev_EK_omegaS_loc_uniform
#print axioms rev_EK_OmegaS_loc_uniform
#print axioms rev_EK_omegaS_uniform
#print axioms rev_EK_OmegaS_uniform
#print axioms rev_moments_loc
#print axioms pal_normal_order_omega
#print axioms pal_normal_order_Omega
#print axioms rev_normal_order_omega
#print axioms rev_normal_order_Omega
#print axioms criterion_moments
#print axioms criterion_EK_omega
#print axioms criterion_EK_Omega
