import GaloisForLFunctions.RHTower.ParitySectorJointRigidity
import GaloisForLFunctions.RHTower.WeilOddBlindPoleWeightWindow

/-!
# RH is pole-free prime-blind positivity on the primitive hyperplane

Generators: odd tests, and even tests whose transform vanishes at `i/2`.  Their real spans make up
the primitive hyperplane `f̂(i/2) + f̂(−i/2) = 0` of real tests.  On every generator the pole weight
`0` removes the pole: `poleWeightArchRe 0 f` is the archimedean energy of an odd test minus its
(nonpositive) pole term, and the archimedean energy itself on an even pole-free test.

**Theorem** (`riemannHypothesis_iff_primeBlindPositiveHyperplane`).  RH holds iff
`Σ_i c_i · poleWeightArchRe 0 (f_i) ≥ 0` for every nonnegative combination of generators whose
autocorrelation values vanish at every `±log n`, `n ≥ 2`.

The statement involves neither primes nor zeros, and no pole term.  On the even pole-free
generators the condition is weaker than prime-blind positivity (`PrimeBlindPositiveAt 1`), and on
the odd generators the pole weight `0` is below the weight `1` of the full Weil functional.

Proof.  Farkas (`exists_of_nonneg_on_null_cone`, using the odd node tests of both signs) identifies
the condition with the existence of weights making the pole-free form nonnegative on all
generators (`exists_hyperplane_weights_iff`).  Joint parity rigidity
(`riemannHypothesis_iff_exists_weilPositiveOddAt_zero_weilPositiveEvenPolar`) says such weights
exist iff RH.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open OddSector WeilOneSided WeilPoleWeight

/-- Even tests whose transform vanishes at `i/2`. -/
def WeilEvenPolarTestFn : Type :=
  {f : WeilTestFn // (∀ x, f.1 (-x) = f.1 x) ∧ paperFT f.1 (I / 2) = 0}

/-- The generators of the primitive hyperplane: odd tests and even pole-free tests. -/
def hyperplaneTest : WeilOddTestFn ⊕ WeilEvenPolarTestFn → WeilTestFn :=
  Sum.elim (fun f => f.1) (fun g => g.1)

/-- **Prime-blind positivity on the primitive hyperplane at pole weight `0`.** -/
def PrimeBlindPositiveHyperplane : Prop :=
  ∀ c : (WeilOddTestFn ⊕ WeilEvenPolarTestFn) →₀ ℝ, (∀ i, 0 ≤ c i) →
    (∀ n : ℕ, 2 ≤ n → (c.sum fun i t => t * logValue (hyperplaneTest i).1 n) = 0) →
    0 ≤ c.sum fun i t => t * poleWeightArchRe 0 (hyperplaneTest i)

theorem re_weilPoleTerm_eq_zero_of_evenPolar (g : WeilEvenPolarTestFn) :
    (weilPoleTerm (EF.weilTest g.1.1 g.1.1)).re = 0 := by
  have h1 : paperFT g.1.1 (-I / 2) = 0 := by
    rw [show (-I / 2 : ℂ) = -(I / 2) by ring, paperFT_neg_of_even g.2.1]; exact g.2.2
  rw [weilPoleTerm_weilTest_eq g.1.2.1.continuous g.1.2.2, g.2.2, h1]; simp

theorem weilPositiveOddAt_zero_and_evenPolar_iff_forall (lam : ℕ → ℝ) :
    (WeilPositiveOddAt 0 lam ∧ WeilPositiveEvenPolar lam) ↔
      ∀ i, linearCombination ℝ (fun j : LogIndex => lam j) (logVector (hyperplaneTest i)) ≤
        poleWeightArchRe 0 (hyperplaneTest i) := by
  constructor
  · rintro ⟨ho, he⟩ (f | g)
    · have h1 := ho f.1.1 f.1.2.1 f.1.2.2 f.2
      rw [re_weilPoleWeightFunctional_eq 0 lam f.1] at h1
      show linearCombination ℝ (fun j : LogIndex => lam j) (logVector f.1) ≤ poleWeightArchRe 0 f.1
      linarith
    · have h1 := he g.1.1 g.1.2.1 g.1.2.2 g.2.1 g.2.2
      rw [re_weilFullFunctional_eq lam g.1] at h1
      show linearCombination ℝ (fun j : LogIndex => lam j) (logVector g.1) ≤ poleWeightArchRe 0 g.1
      unfold poleWeightArchRe
      rw [re_weilPoleTerm_eq_zero_of_evenPolar g]
      linarith
  · intro h
    refine ⟨fun f hf hfc hodd => ?_, fun f hf hfc heven h0 => ?_⟩
    · have h1 : linearCombination ℝ (fun j : LogIndex => lam j) (logVector ⟨f, hf, hfc⟩) ≤
          poleWeightArchRe 0 ⟨f, hf, hfc⟩ := h (Sum.inl ⟨⟨f, hf, hfc⟩, hodd⟩)
      rw [re_weilPoleWeightFunctional_eq 0 lam ⟨f, hf, hfc⟩]
      exact sub_nonneg.mpr h1
    · have h1 : linearCombination ℝ (fun j : LogIndex => lam j) (logVector ⟨f, hf, hfc⟩) ≤
          poleWeightArchRe 0 ⟨f, hf, hfc⟩ := h (Sum.inr ⟨⟨f, hf, hfc⟩, heven, h0⟩)
      have hp : (weilPoleTerm (EF.weilTest f f)).re = 0 :=
        re_weilPoleTerm_eq_zero_of_evenPolar ⟨⟨f, hf, hfc⟩, heven, h0⟩
      have h2 : poleWeightArchRe 0 ⟨f, hf, hfc⟩ = weilArchRe (EF.weilTest f f) := by
        unfold poleWeightArchRe
        change weilArchRe (EF.weilTest f f) + (0 - 1) * (weilPoleTerm (EF.weilTest f f)).re = _
        rw [hp]; ring
      rw [re_weilFullFunctional_eq lam ⟨f, hf, hfc⟩]
      change 0 ≤ weilArchRe (EF.weilTest f f) - _
      linarith

/-- **Farkas on the primitive hyperplane.** -/
theorem exists_hyperplane_weights_iff :
    (∃ lam : ℕ → ℝ, WeilPositiveOddAt 0 lam ∧ WeilPositiveEvenPolar lam) ↔
      PrimeBlindPositiveHyperplane := by
  constructor
  · rintro ⟨lam, hlam⟩ c hc hnull
    have hall := (weilPositiveOddAt_zero_and_evenPolar_iff_forall lam).mp hlam
    have hsum : (c.sum fun i t => t • logVector (hyperplaneTest i)) = 0 := by
      ext j
      rw [Finsupp.sum_apply, Finsupp.coe_zero, Pi.zero_apply, ← hnull j j.2]
      refine Finsupp.sum_congr fun i _ => ?_
      rw [Finsupp.smul_apply, logVector_apply, smul_eq_mul]
    have hlin : (c.sum fun i t => linearCombination ℝ (fun j : LogIndex => lam j)
        (t • logVector (hyperplaneTest i))) = 0 := by
      rw [← map_finsuppSum, hsum, map_zero]
    have h1 : (c.sum fun i t => linearCombination ℝ (fun j : LogIndex => lam j)
        (t • logVector (hyperplaneTest i))) ≤
        c.sum fun i t => t * poleWeightArchRe 0 (hyperplaneTest i) := by
      refine Finset.sum_le_sum fun i _ => ?_
      show linearCombination ℝ (fun j : LogIndex => lam j) (c i • logVector (hyperplaneTest i)) ≤
        c i * poleWeightArchRe 0 (hyperplaneTest i)
      rw [map_smul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hall i) (hc i)
    linarith
  · intro h
    have hsqrt : ∀ j : LogIndex, 0 < Real.sqrt (j : ℕ) := fun j =>
      Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le two_pos j.2))
    obtain ⟨lam, hlam⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone
      (fun i => logVector (hyperplaneTest i)) (fun i => poleWeightArchRe 0 (hyperplaneTest i))
      (fun j => ⟨Sum.inl (oddMinus j), _, div_pos (mul_pos two_pos
        (integral_evenProfile_sq_pos j)) (hsqrt j), logVector_oddMinus j⟩)
      (fun j => ⟨Sum.inl (oddPlus j), _, div_pos (mul_pos two_pos
        (integral_oddProfile_sq_pos j)) (hsqrt j), logVector_oddPlus j⟩)
      (fun c hc hnull => by
        have e : linearCombination ℝ (fun i => poleWeightArchRe 0 (hyperplaneTest i)) c =
            c.sum fun i t => t * poleWeightArchRe 0 (hyperplaneTest i) := by
          rw [linearCombination_apply]; simp only [smul_eq_mul]
        rw [e]
        refine h c hc fun n hn => ?_
        have h0 := congrArg (fun v : LogIndex →₀ ℝ => v ⟨n, hn⟩) hnull
        simp only [linearCombination_apply, Finsupp.sum_apply, Finsupp.smul_apply,
          logVector_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h0
        exact h0)
    refine ⟨fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0,
      (weilPositiveOddAt_zero_and_evenPolar_iff_forall _).mpr fun i => ?_⟩
    have e : (fun j : LogIndex => (fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0) (j : ℕ)) =
        lam := funext fun j => by simp [j.2]
    rw [e]
    exact hlam i

/-- **RH is pole-free prime-blind positivity on the primitive hyperplane.** -/
theorem riemannHypothesis_iff_primeBlindPositiveHyperplane :
    RiemannHypothesis ↔ PrimeBlindPositiveHyperplane :=
  riemannHypothesis_iff_exists_weilPositiveOddAt_zero_weilPositiveEvenPolar.trans
    exists_hyperplane_weights_iff

end RHTower.EvenSector

end
