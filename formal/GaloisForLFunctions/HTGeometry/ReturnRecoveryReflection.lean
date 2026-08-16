import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Return recovery and complexity reflection

A semigroup whose full return `S * T` is `δ`-close to the identity reflects every approximation
across the return: a dictionary element `G` approximating `T` to `ε` has its inverse approximating
`S` to `ε + δ`.  Only two metric facts are used -- left composition contracts distance, and right
composition by a dictionary element is an isometry -- so the statement is a monoid-metric one and
holds verbatim for channels in diamond distance.

At fixed word length the reflection is injective, so it interlaces the normalised incidence
counts, and therefore every nonnegative length partition function built from them.

Separately, an approximate return forces a lower bound on distinguishability: if the return factors
through a norm contraction, no intermediate stage can lose more than `δ` of any norm.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {M : Type*} [Monoid M] [MetricSpace M]

/-- Left composition contracts the metric.  For quantum channels in diamond distance this is
complete positivity plus trace preservation. -/
def LeftContracting (M : Type*) [Monoid M] [MetricSpace M] : Prop :=
  ∀ a b c : M, dist (c * a) (c * b) ≤ dist a b

/-- **Reflection across an approximate return.**  If `S * T` is `δ`-close to the identity and the
invertible element `G` is `ε`-close to `T`, then `S` is `(ε + δ)`-close to `G⁻¹`. -/
theorem dist_reflect_le (hleft : LeftContracting M) {S T G Gi : M} {δ ε : ℝ}
    (hiso : ∀ a b : M, dist (a * G) (b * G) = dist a b) (hGi : Gi * G = 1)
    (hret : dist (S * T) 1 ≤ δ) (hW : dist G T ≤ ε) :
    dist S Gi ≤ ε + δ := by
  have h1 : dist (S * G) (S * T) ≤ ε := le_trans (hleft G T S) hW
  have h2 : dist (S * G) 1 ≤ ε + δ := by
    have := dist_triangle (S * G) (S * T) 1
    linarith
  calc dist S Gi = dist (S * G) (Gi * G) := (hiso S Gi).symm
    _ = dist (S * G) 1 := by rw [hGi]
    _ ≤ ε + δ := h2

/-- **Complexity reflection.**  A dictionary word realising `T` at radius `ε` realises `S` at
radius `ε + δ` after inversion, so the two complexities interlace. -/
theorem exists_reflected_word (hleft : LeftContracting M) {S T G Gi : M} {δ ε : ℝ}
    (hiso : ∀ a b : M, dist (a * G) (b * G) = dist a b) (hGi : Gi * G = 1)
    (hret : dist (S * T) 1 ≤ δ) (hW : dist G T ≤ ε) :
    dist Gi S ≤ ε + δ := by
  rw [dist_comm]
  exact dist_reflect_le hleft hiso hGi hret hW

/-- **Incidence interlacing.**  At each exact word length the reflection is an injection of the
`ε`-incidence set of `T` into the `(ε + δ)`-incidence set of `S`. -/
theorem card_reflect_le {W : Type*} [Fintype W] [DecidableEq W] (word : W → M) (inv : W → W)
    (hleft : LeftContracting M) {S T : M} {δ ε : ℝ} (hret : dist (S * T) 1 ≤ δ)
    (hiso : ∀ w : W, ∀ a b : M, dist (a * word w) (b * word w) = dist a b)
    (hinv : ∀ w : W, word (inv w) * word w = 1) (hinj : Function.Injective inv) :
    (Finset.univ.filter fun w => dist (word w) T ≤ ε).card
      ≤ (Finset.univ.filter fun w => dist (word w) S ≤ ε + δ).card := by
  classical
  refine Finset.card_le_card_of_injOn inv (fun w hw => ?_) (fun a _ b _ h => hinj h)
  have hw' : dist (word w) T ≤ ε := (Finset.mem_filter.mp hw).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  exact exists_reflected_word hleft (hiso w) (hinv w) hret hw'

/-- **No stage loses more than the return defect.**  If the return factors through a norm
contraction, every intermediate stage keeps at least `1 - δ` of any norm. -/
theorem norm_le_of_contraction_return {E : Type*} [NormedAddCommGroup E] {f g h : E → E}
    (hcontr : ∀ x, ‖h x‖ ≤ ‖x‖) (hcomp : ∀ x, g x = h (f x)) {δ : ℝ}
    (hret : ∀ x, ‖g x - x‖ ≤ δ * ‖x‖) (x : E) :
    (1 - δ) * ‖x‖ ≤ ‖f x‖ := by
  have h1 : ‖g x‖ ≤ ‖f x‖ := by
    rw [hcomp x]
    exact hcontr (f x)
  have h2 : ‖x‖ - ‖g x‖ ≤ ‖g x - x‖ := by
    have := norm_sub_norm_le x (g x)
    rwa [norm_sub_rev] at this
  have h3 := hret x
  nlinarith [h1, h2, h3]

end GaloisForLFunctions.HTGeometry
