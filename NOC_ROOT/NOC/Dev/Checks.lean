
import Mathlib
import NOC.All
/-!
Module: NOC.Dev.Checks
Summary: Small smoke tests to ensure key lemmas elaborate. Useful while developing.
-/

open NOC

-- quick smoke checks (these should elaborate)
#check NOC.lemmaA_freeEnergy_nonneg_product
#check NOC.lemmaB_affine_link
#check NOC.lemmaB_link_from_quadratic_supports
#check NOC.lemmaB_local_nonneg
#check NOC.lemmaB_expected_nonneg_finset
#check NOC.quad_f_step_abs_le_general
#check NOC.hb_delta2f_nonpos_of_small_rel_step
#check NOC.lemmaB_HB_affine_capacity
