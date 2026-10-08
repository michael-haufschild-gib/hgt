import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorFiniteDeficit
import GaloisForLFunctions.RHTower.WeilConeSingularDeficitEnvelope
import GaloisForLFunctions.HTGeometry.LogarithmicResidueQuantization

/-!
# The exact signed logarithmic residue of a cubic datum

Subtracting one xi logarithmic derivative counts the one-xi deficit exactly.
The right-half-plane identity retains two copies of the archimedean datum.
The complete cubic correspondence therefore gives rigidity or infinitely many
negative integer residues, without any simplicity or xi-RH assumption.
-/

open Complex Filter Topology Set

noncomputable section

namespace RHTower.WeilHigherDenominator

/-- The logarithmic derivative relative to one complete xi divisor. -/
def xiRelativeLogDeriv (E : ℂ → ℂ) (s : ℂ) : ℂ := logDeriv E s - logDeriv xi s

/-- The signed order, before taking its negative part. -/
def xiLogResidue (E : ℂ → ℂ) (ρ : ℂ) : ℤ :=
  (analyticOrderNatAt E ρ : ℤ) - analyticOrderNatAt xi ρ

/-- Points with a strictly negative integer punctured residue. -/
def negativeIntegralResidueSet (F : ℂ → ℂ) : Set ℂ :=
  {ρ | ∃ d : ℕ, 0 < d ∧
    Tendsto (fun s => (s - ρ) * F s) (𝓝[≠] ρ) (𝓝 (-(d : ℂ)))}

private theorem logDeriv_residue_of_entire {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf1 : f 1 ≠ 0) (ρ : ℂ) :
    Tendsto (fun s => (s - ρ) * logDeriv f s) (𝓝[≠] ρ)
      (𝓝 (analyticOrderNatAt f ρ : ℂ)) := by
  have ha : AnalyticAt ℂ f ρ := hf.differentiableOn.analyticAt Filter.univ_mem
  have hfin : analyticOrderAt f ρ ≠ ⊤ := by
    intro ht
    have hz := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ
      (fun z => hf.differentiableOn.analyticAt Filter.univ_mem)).mp ht
    exact hf1 (congrFun hz 1)
  have ho : meromorphicOrderAt f ρ = ((analyticOrderNatAt f ρ : ℤ) : WithTop ℤ) := by
    rw [ha.meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hfin]
    rfl
  simpa using
    GaloisForLFunctions.HTGeometry.logDeriv_residue_of_meromorphicOrder ha.meromorphicAt ho

/-- The signed order is the actual punctured analytic residue, including at common zeros. -/
theorem xiRelativeLogDeriv_residue {E : ℂ → ℂ}
    (hE : Differentiable ℂ E) (hE1 : E 1 ≠ 0) (ρ : ℂ) :
    Tendsto (fun s => (s - ρ) * xiRelativeLogDeriv E s) (𝓝[≠] ρ)
      (𝓝 (xiLogResidue E ρ : ℂ)) := by
  have hξ1 : xi 1 ≠ 0 := by rw [xi_one]; norm_num
  have hξ := logDeriv_residue_of_entire xi_differentiable hξ1 ρ
  simpa [xiRelativeLogDeriv, xiLogResidue, mul_sub] using
    (logDeriv_residue_of_entire hE hE1 ρ).sub hξ

/-- The negative residue weight is exactly the existing one-xi deficit. -/
theorem xiLogResidue_negativePart (E : ℂ → ℂ) (ρ : ℂ) :
    (-xiLogResidue E ρ).toNat = xiDeficit E ρ := by
  unfold xiLogResidue xiDeficit
  omega

/-- Finite windows retain every missing multiplicity. -/
theorem sum_xiLogResidue_negativePart (E : ℂ → ℂ) (S : Finset ℂ) :
    ∑ ρ ∈ S, (-xiLogResidue E ρ).toNat = ∑ ρ ∈ S, xiDeficit E ρ := by
  simp only [xiLogResidue_negativePart]

/-- Negative analytic residues occur at exactly the deficit support. -/
theorem negativeIntegralResidueSet_xiRelativeLogDeriv {E : ℂ → ℂ}
    (hE : Differentiable ℂ E) (hE1 : E 1 ≠ 0) :
    negativeIntegralResidueSet (xiRelativeLogDeriv E) = xiDeficitSupport E := by
  ext ρ
  constructor
  · rintro ⟨d, hd, ht⟩
    have heq := tendsto_nhds_unique (xiRelativeLogDeriv_residue hE hE1 ρ) ht
    have hi : xiLogResidue E ρ = -(d : ℤ) := by exact_mod_cast heq
    change analyticOrderNatAt E ρ < analyticOrderNatAt xi ρ
    unfold xiLogResidue at hi
    omega
  · intro hρ
    change analyticOrderNatAt E ρ < analyticOrderNatAt xi ρ at hρ
    have hd : 0 < xiDeficit E ρ := by unfold xiDeficit; omega
    refine ⟨xiDeficit E ρ, hd, ?_⟩
    have hi : xiLogResidue E ρ = -(xiDeficit E ρ : ℤ) := by
      unfold xiLogResidue xiDeficit
      omega
    simpa only [hi, Int.cast_neg, Int.cast_natCast] using
      xiRelativeLogDeriv_residue hE hE1 ρ

/-- Removing one xi keeps two archimedean copies on the Dirichlet side. -/
theorem xiRelativeLogDeriv_eq_arithmetic {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E)
    (hRH : ∀ s, E s = 0 → s.re = 1 / 2) {lam : ℕ → ℝ}
    (hΛ : ∀ s : ℂ, 1 < s.re →
      deriv (LSeries g) s = -(3 : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s)
    {s : ℂ} (hs : 1 < s.re) :
    xiRelativeLogDeriv E s =
      2 * (zetaArchimedeanDatum s + 1 / (s - 1)) -
        3 * LSeries (WeilHerglotz.lamC lam) s +
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  have hEs : E s ≠ 0 := by
    intro h0
    have hhalf := hRH s h0
    linarith
  rw [xiRelativeLogDeriv, WeilZetaPower.logDeriv_eq_mul_weilFunction hD hΛ hs hEs,
    WeilSpectral.logDeriv_xi_eq_datum hs]
  unfold WeilHerglotz.weilFunction zetaArchimedeanDatum
  push_cast
  ring

/-- The original complete correspondence gives rigidity or infinitely many negative residues. -/
theorem degreeThree_eq_vonMangoldt_or_infinite_negativeLogResidues
    {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0)
    (hRH : ∀ s, E s = 0 → s.re = 1 / 2) {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΛ : ∀ s : ℂ, 1 < s.re →
      deriv (LSeries g) s = -(3 : ℂ) * LSeries (WeilHerglotz.lamC lam) s * LSeries g s) :
    ((∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis) ∨
      (negativeIntegralResidueSet (xiRelativeLogDeriv E)).Infinite := by
  rw [negativeIntegralResidueSet_xiRelativeLogDeriv hD.entire hE1]
  exact degreeThree_eq_vonMangoldt_or_infiniteDeficits hD hE1 hRH hsl hΛ

end RHTower.WeilHigherDenominator
