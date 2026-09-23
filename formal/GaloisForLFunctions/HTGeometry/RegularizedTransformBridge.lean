import GaloisForLFunctions.HTGeometry.HypertranscendentalAddConst

/-!
# Constant-shift invariance of hypertranscendence

A transform differing from another by a quantity independent of the spectral variable has the same
hypertranscendence status.

WARNING — this is NOT the Herglotz regularization bridge.  The (H0) regularization is a genuine
RATIONAL gauge, not a constant shift: `regularizedHerglotzTransform_eq` shows the regularized
transform equals `z * (total mass) + (1 + z ^ (2 : ℕ)) * (Cauchy transform of the Nevanlinna-weighted
measure)`.  Splitting the regularized integral into a Cauchy integral minus a constant is invalid,
because under (H0) the individual pieces need not converge — which is the reason the regularization
exists.  The correct bridge is `hypertranscendentalOver_herglotzGauge_iff`, already in the tree.

These lemmas are retained for the genuine constant-shift situations they do describe.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **A constant-shifted transform has the same hypertranscendence status.** -/
theorem hypertranscendental_of_eq_add_const {F G : ℂ → ℂ} (K : ℂ)
    (hreg : ∀ z, G z = F z + K) :
    Hypertranscendental G ↔ Hypertranscendental F := by
  have hfun : G = fun z => F z + K := funext hreg
  rw [hfun]
  exact hypertranscendental_add_const_iff K

/-- **Subtracting a constant preserves hypertranscendence.** -/
theorem hypertranscendental_sub_const_iff {F : ℂ → ℂ} (K : ℂ) :
    Hypertranscendental (fun z => F z - K) ↔ Hypertranscendental F := by
  refine hypertranscendental_of_eq_add_const (-K) ?_
  intro z
  ring

/-- A transform presented as another minus a constant.  See the module warning: this is not the
Herglotz (H0) regularization, which is a rational gauge. -/
theorem hypertranscendental_sub_const_presentation_iff
    (cauchy : ℂ → ℂ) (reg : ℂ) (m : ℂ → ℂ) (hm : ∀ z, m z = cauchy z - reg) :
    Hypertranscendental m ↔ Hypertranscendental cauchy := by
  have hfun : m = fun z => cauchy z - reg := funext hm
  rw [hfun]
  exact hypertranscendental_sub_const_iff reg

end

end GaloisForLFunctions.HTGeometry
