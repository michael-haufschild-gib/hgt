import GaloisForLFunctions.TransHorizonIncidenceMechanics.CriticalWienerConvolutionsPreserveTheReceiver

/-!
# Payment is bounded cofactor action

Convolution changes the cofactor packet only by the mean times the kernel's own
centered prefix. Every critical Wiener kernel pays this correction uniformly,
so payment of the convolution is equivalent to bounded packet norm.
-/

noncomputable section
open Finset RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The full finite cofactor action on a source centered by its actual mean. -/
def cofactorPrefixAction (c k : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 n, k j * weightCenteredPrefix c (∑' d : ℕ, c d / d) (n / j)

/-- The exact centered convolution law, with the actual absolutely convergent means. -/
theorem cofactorPrefixAction_eq_convolution_sub_mean (c k : ℕ → ℝ)
    (hc : Summable fun n : ℕ => |c n / n|) (hk : CriticalWiener k) (n : ℕ) :
    cofactorPrefixAction c k n =
      weightCenteredPrefix (dirichletConv k c) (∑' d : ℕ, dirichletConv k c d / d) n -
        (∑' d : ℕ, c d / d) * weightCenteredPrefix k (∑' d : ℕ, k d / d) n := by
  have hm := (hasSum_dirichletConv_div hk.summable_abs_div.of_abs.hasSum hc.of_abs.hasSum
    hk.summable_abs_div hc).tsum_eq
  rw [hm, weightCenteredPrefix_dirichletConv]
  simp only [cofactorPrefixAction]
  ring

/-- A critical Wiener kernel repairs exactly when its full cofactor action has bounded norm. -/
theorem receiverBounded_dirichletConv_iff_cofactorNorm (c k : ℕ → ℝ)
    (hc : Summable fun n : ℕ => |c n / n|) (hk : CriticalWiener k) :
    ReceiverBounded (dirichletConv k c) ↔
      ∃ C : ℝ, ∀ T : ℕ, pronicNorm (cofactorPrefixAction c k) T ≤ C := by
  let m : ℝ := ∑' d : ℕ, c d / d
  let K : ℝ := (Real.sqrt 2 + 1) * ∑' d : ℕ, |k d| * (d : ℝ) ^ (-(1 / 2 : ℝ))
  have hkernel (T : ℕ) : pronicNorm
      (weightCenteredPrefix k (∑' d : ℕ, k d / d)) T ≤ K :=
    pronicNorm_weightCenteredPrefix_le_critical hk T
  have hsub : cofactorPrefixAction c k = fun n =>
      weightCenteredPrefix (dirichletConv k c) (∑' d : ℕ, dirichletConv k c d / d) n +
        (-m) * weightCenteredPrefix k (∑' d : ℕ, k d / d) n := by
    funext n
    rw [cofactorPrefixAction_eq_convolution_sub_mean c k hc hk]
    dsimp only [m]
    ring
  have hadd : weightCenteredPrefix (dirichletConv k c)
      (∑' d : ℕ, dirichletConv k c d / d) = fun n =>
        cofactorPrefixAction c k n + m * weightCenteredPrefix k (∑' d : ℕ, k d / d) n := by
    funext n
    rw [cofactorPrefixAction_eq_convolution_sub_mean c k hc hk]
    dsimp only [m]
    ring
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨Real.sqrt B + |m| * K, fun T => ?_⟩
    have hconv : pronicNorm (weightCenteredPrefix (dirichletConv k c)
        (∑' d : ℕ, dirichletConv k c d / d)) T ≤ Real.sqrt B :=
      Real.sqrt_le_sqrt (hB T)
    rw [hsub]
    refine (pronicNorm_add_le _ _ T).trans ?_
    rw [pronicNorm_smul, abs_neg]
    exact add_le_add hconv (mul_le_mul_of_nonneg_left (hkernel T) (abs_nonneg m))
  · rintro ⟨C, hC⟩
    refine ⟨(C + |m| * K) ^ 2, fun T => ?_⟩
    rw [weightPronicEnergy_eq_sq_pronicNorm]
    apply pow_le_pow_left₀ (pronicNorm_nonneg _ T) _ 2
    rw [hadd]
    refine (pronicNorm_add_le _ _ T).trans ?_
    rw [pronicNorm_smul]
    exact add_le_add (hC T) (mul_le_mul_of_nonneg_left (hkernel T) (abs_nonneg m))

end GaloisForLFunctions.BiarithmeticGeometry
