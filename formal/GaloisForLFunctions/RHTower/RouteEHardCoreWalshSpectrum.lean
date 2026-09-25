import GaloisForLFunctions.RHTower.RouteEHardCorePairField
import GaloisForLFunctions.HTGeometry.BiasedWalshInteractionMechanics

/-!
# Möbius-grade spectrum of the Route E hard-core transition

The source-faithful coprime transition forces an occupied prime to be absent
on the other leg; an unoccupied prime enters with probability `1/p`.
Every centered Bernoulli interaction character is an eigenfunction with
eigenvalue `∏ p ∈ K, -1/p`, the finite squarefree Möbius sign divided by its
prime radical. This is an exact source-side spectral law, not a physical-shell
or RH estimate.
-/

open scoped BigOperators

namespace RHTower

open HTGeometry.ConstraintFrameRelativity
open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Independent receiver occupation under the hard-core coprime transition. -/
def routeEHardCoreTransition (p : ι → ℝ) (S : Finset ι) (i : ι) : ℝ :=
  if i ∈ S then 0 else 1 / p i

/-- Unnormalized biased Walsh character for the critical source `q_i = 1/(p_i+1)`. -/
def routeEHardCoreWalsh (p : ι → ℝ) (K T : Finset ι) : ℝ :=
  (∏ i ∈ T, if i ∈ K then 1 - 1 / (p i + 1) else 1) *
    ∏ i ∈ Tᶜ, if i ∈ K then -(1 / (p i + 1)) else 1

/-- Exact diagonal action of the coprime transition on every Walsh grade. -/
theorem routeEHardCoreWalsh_eigen
    (p : ι → ℝ) (hp : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i + 1 ≠ 0)
    (K S : Finset ι) :
    bernoulliExp (routeEHardCoreTransition p S) (routeEHardCoreWalsh p K) =
      (∏ i ∈ K, -(1 / p i)) * routeEHardCoreWalsh p K S := by
  let f : ι → ℝ := fun i => if i ∈ K then 1 - 1 / (p i + 1) else 1
  let g : ι → ℝ := fun i => if i ∈ K then -(1 / (p i + 1)) else 1
  have hlocal (i : ι) :
      routeEHardCoreTransition p S i * f i +
        (1 - routeEHardCoreTransition p S i) * g i =
      (if i ∈ K then -(1 / p i) else 1) *
        (if i ∈ S then f i else g i) := by
    by_cases hiK : i ∈ K <;> by_cases hiS : i ∈ S
    · simp only [f, g, hiK, hiS, ite_true, routeEHardCoreTransition]
      field_simp [hp i, hp1 i]
      ring
    · simp only [f, g, hiK, hiS, ite_true, ite_false, routeEHardCoreTransition]
      field_simp [hp i, hp1 i]
      ring
    · simp [f, g, hiK, hiS, routeEHardCoreTransition]
    · simp [f, g, hiK, hiS, routeEHardCoreTransition]
  have hsplit : (∏ i, if i ∈ S then f i else g i) =
      (∏ i ∈ S, f i) * ∏ i ∈ Sᶜ, g i := by
    have hfilter : (Finset.univ.filter fun i => i ∉ S) = Sᶜ := by
      ext i
      simp
    simpa [hfilter] using (Finset.prod_ite (s := Finset.univ) (p := fun i => i ∈ S) f g)
  have hprod := bernoulliExp_prod (routeEHardCoreTransition p S) f g
  calc
    _ = ∏ i, (routeEHardCoreTransition p S i * f i +
        (1 - routeEHardCoreTransition p S i) * g i) := by
          change bernoulliExp (routeEHardCoreTransition p S)
            (fun T => (∏ i ∈ T, f i) * ∏ i ∈ Tᶜ, g i) = _
          exact hprod
    _ = ∏ i, ((if i ∈ K then -(1 / p i) else 1) *
        (if i ∈ S then f i else g i)) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hlocal i
    _ = (∏ i ∈ K, -(1 / p i)) * routeEHardCoreWalsh p K S := by
          rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, hsplit]
          rfl

/-- Closed prime-indexed form: no analytic or RH hypotheses. -/
theorem routeEHardCorePrimeWalsh_eigen (P : Finset Nat.Primes)
    (K S : Finset {p : Nat.Primes // p ∈ P}) :
    bernoulliExp
        (routeEHardCoreTransition (fun i : {p : Nat.Primes // p ∈ P} =>
          ((i.1 : ℕ) : ℝ)) S)
        (routeEHardCoreWalsh (fun i : {p : Nat.Primes // p ∈ P} =>
          ((i.1 : ℕ) : ℝ)) K) =
      (∏ i ∈ K, -(1 / (((i.1 : ℕ) : ℝ)))) *
        routeEHardCoreWalsh (fun i : {p : Nat.Primes // p ∈ P} =>
          ((i.1 : ℕ) : ℝ)) K S := by
  classical
  apply routeEHardCoreWalsh_eigen
  · intro i
    exact ne_of_gt (by exact_mod_cast i.1.2.pos)
  · intro i
    have hi : (0 : ℝ) < ((i.1 : ℕ) : ℝ) := by exact_mod_cast i.1.2.pos
    linarith

/-- The same eigenlaw on the corpus's normalized biased Walsh basis. -/
theorem routeEHardCoreBiasedWalsh_eigen
    (p : ι → ℝ) (hp : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i + 1 ≠ 0)
    (K S : Finset ι) :
    let q : ι → ℝ := fun i => 1 / (p i + 1)
    bernoulliExp (routeEHardCoreTransition p S) (biasedWalshCharacter q K) =
      (∏ i ∈ K, -(1 / p i)) * biasedWalshCharacter q K S := by
  let q : ι → ℝ := fun i => 1 / (p i + 1)
  let f : ι → ℝ := fun i => if i ∈ K then
    (1 - q i) / Real.sqrt (biasedBernoulliVariance q i) else 1
  let g : ι → ℝ := fun i => if i ∈ K then
    -q i / Real.sqrt (biasedBernoulliVariance q i) else 1
  have hlocal (i : ι) :
      routeEHardCoreTransition p S i * f i +
        (1 - routeEHardCoreTransition p S i) * g i =
      (if i ∈ K then -(1 / p i) else 1) *
        (if i ∈ S then f i else g i) := by
    by_cases hiK : i ∈ K <;> by_cases hiS : i ∈ S
    · simp only [f, g, q, hiK, hiS, ite_true, routeEHardCoreTransition]
      field_simp [hp i, hp1 i]
      ring
    · simp only [f, g, q, hiK, hiS, ite_true, ite_false, routeEHardCoreTransition]
      field_simp [hp i, hp1 i]
      ring
    · simp [f, g, hiK, hiS, routeEHardCoreTransition]
    · simp [f, g, hiK, hiS, routeEHardCoreTransition]
  have hsplit : (∏ i, if i ∈ S then f i else g i) =
      (∏ i ∈ S, f i) * ∏ i ∈ Sᶜ, g i := by
    have hfilter : (Finset.univ.filter fun i => i ∉ S) = Sᶜ := by
      ext i
      simp
    simpa [hfilter] using (Finset.prod_ite (s := Finset.univ) (p := fun i => i ∈ S) f g)
  have hprod := bernoulliExp_prod (routeEHardCoreTransition p S) f g
  dsimp only
  calc
    _ = ∏ i, (routeEHardCoreTransition p S i * f i +
        (1 - routeEHardCoreTransition p S i) * g i) := by
          change bernoulliExp (routeEHardCoreTransition p S)
            (fun T => (∏ i ∈ T, f i) * ∏ i ∈ Tᶜ, g i) = _
          exact hprod
    _ = ∏ i, ((if i ∈ K then -(1 / p i) else 1) *
        (if i ∈ S then f i else g i)) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hlocal i
    _ = (∏ i ∈ K, -(1 / p i)) * biasedWalshCharacter q K S := by
          rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, hsplit]
          rfl

/-- Reversible hard-core transition applied to an arbitrary Boolean observable. -/
def routeEHardCoreOperator (p : ι → ℝ) (f : Finset ι → ℝ)
    (S : Finset ι) : ℝ :=
  bernoulliExp (routeEHardCoreTransition p S) f

/-- Exact quadratic-form spectrum: odd grades carry negative Möbius sign,
even grades positive. The physical source may excite both. -/
theorem routeEHardCoreQuadratic_eq_walshSpectrum
    (p : ι → ℝ) (hp : ∀ i, 0 < p i) (f : Finset ι → ℝ) :
    let q : ι → ℝ := fun i => 1 / (p i + 1)
    bernoulliExp q (fun S => f S * routeEHardCoreOperator p f S) =
      ∑ K : Finset ι,
        (∏ i ∈ K, -(1 / p i)) * (biasedWalshCoefficient q f K) ^ 2 := by
  let q : ι → ℝ := fun i => 1 / (p i + 1)
  have hq0 : ∀ i, 0 < q i := by
    intro i
    dsimp [q]
    exact div_pos zero_lt_one (by linarith [hp i])
  have hq1 : ∀ i, q i < 1 := by
    intro i
    dsimp [q]
    rw [div_lt_iff₀ (by linarith [hp i] : 0 < p i + 1)]
    linarith [hp i]
  have hpoint (S : Finset ι) :
      routeEHardCoreOperator p f S =
        ∑ K : Finset ι,
          ((∏ i ∈ K, -(1 / p i)) * biasedWalshCoefficient q f K) *
            biasedWalshCharacter q K S := by
    let r := routeEHardCoreTransition p S
    calc
      routeEHardCoreOperator p f S =
          bernoulliExp r (fun T => ∑ K : Finset ι,
            biasedWalshCoefficient q f K * biasedWalshCharacter q K T) := by
              unfold routeEHardCoreOperator
              apply congrArg
              funext T
              exact (biasedWalsh_reconstruction hq0 hq1 f T).symm
      _ = ∑ K : Finset ι,
          biasedWalshCoefficient q f K *
            bernoulliExp r (biasedWalshCharacter q K) := by
              rw [bernoulliExp_sum]
              apply Finset.sum_congr rfl
              intro K hK
              exact bernoulliExp_smul r _ _
      _ = ∑ K : Finset ι,
          ((∏ i ∈ K, -(1 / p i)) * biasedWalshCoefficient q f K) *
            biasedWalshCharacter q K S := by
              apply Finset.sum_congr rfl
              intro K hK
              rw [routeEHardCoreBiasedWalsh_eigen p
                (fun i => (hp i).ne')
                (fun i => ne_of_gt (by linarith [hp i] : 0 < p i + 1)) K S]
              ring
  dsimp only
  calc
    bernoulliExp q (fun S => f S * routeEHardCoreOperator p f S) =
        bernoulliExp q (fun S => ∑ K : Finset ι,
          ((∏ i ∈ K, -(1 / p i)) * biasedWalshCoefficient q f K) *
            (f S * biasedWalshCharacter q K S)) := by
            apply congrArg
            funext S
            rw [hpoint]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro K hK
            ring
    _ = ∑ K : Finset ι,
        ((∏ i ∈ K, -(1 / p i)) * biasedWalshCoefficient q f K) *
          bernoulliExp q (fun S => f S * biasedWalshCharacter q K S) := by
            rw [bernoulliExp_sum]
            apply Finset.sum_congr rfl
            intro K hK
            exact bernoulliExp_smul q _ _
    _ = ∑ K : Finset ι,
        (∏ i ∈ K, -(1 / p i)) * (biasedWalshCoefficient q f K) ^ 2 := by
            apply Finset.sum_congr rfl
            intro K hK
            change ((∏ i ∈ K, -(1 / p i)) * biasedWalshCoefficient q f K) *
              biasedWalshCoefficient q f K = _
            ring

/-- Closed finite-prime quadratic identity, using the existing normalized
Bernoulli Walsh coefficients. -/
theorem routeEHardCorePrimeQuadratic_eq_walshSpectrum
    (P : Finset Nat.Primes) (f : Finset {p : Nat.Primes // p ∈ P} → ℝ) :
    let v : {p : Nat.Primes // p ∈ P} → ℝ := fun i => ((i.1 : ℕ) : ℝ)
    let q : {p : Nat.Primes // p ∈ P} → ℝ := fun i => 1 / (v i + 1)
    bernoulliExp q (fun S => f S * routeEHardCoreOperator v f S) =
      ∑ K : Finset {p : Nat.Primes // p ∈ P},
        (∏ i ∈ K, -(1 / v i)) * (biasedWalshCoefficient q f K) ^ 2 := by
  classical
  exact routeEHardCoreQuadratic_eq_walshSpectrum
    (p := fun i : {p : Nat.Primes // p ∈ P} => ((i.1 : ℕ) : ℝ))
    (fun i => by exact_mod_cast i.1.2.pos) f

end

end RHTower
