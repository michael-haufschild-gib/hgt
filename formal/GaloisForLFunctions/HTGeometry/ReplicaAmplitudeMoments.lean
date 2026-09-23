import GaloisForLFunctions.HTGeometry.ReplicaActionCrowdingShortcutLaw

/-!
# The replica amplitude recursion and the moments of the replica energy

A replica multiplicity vector of mass `r + 1` is obtained from one of mass `r` by incrementing a
single coordinate, and Pascal's rule for multinomial coefficients says the amplitudes add up
correctly along that step.  This gives a recursion for every weighted sum over multiplicity vectors,
from which the total mass, the mean replica energy and its second moment follow by induction.

The conclusion is that the replica energy of order `r` has total mass one, mean `r` times the single
level mean, and variance exactly `r` times the single level variance — the exact finite statement
that a sum of `r` independent samples obeys, proved without any measure-theoretic independence.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {I : Type*} [Fintype I] [DecidableEq I]

/-! ## Splitting a sum or product at one coordinate -/

private theorem sum_update_split {M : Type*} [AddCommMonoid M] (F : I → ℕ → M)
    (p : I → ℕ) (i : I) (v : ℕ) :
    ∑ j, F j (Function.update p i v j) = F i v + ∑ j ∈ Finset.univ.erase i, F j (p j) := by
  rw [← Finset.add_sum_erase Finset.univ
    (fun j => F j (Function.update p i v j)) (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem prod_update_split {M : Type*} [CommMonoid M] (F : I → ℕ → M)
    (p : I → ℕ) (i : I) (v : ℕ) :
    ∏ j, F j (Function.update p i v j) = F i v * ∏ j ∈ Finset.univ.erase i, F j (p j) := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => F j (Function.update p i v j)) (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem sum_split {M : Type*} [AddCommMonoid M] (F : I → ℕ → M) (p : I → ℕ) (i : I) :
    ∑ j, F j (p j) = F i (p i) + ∑ j ∈ Finset.univ.erase i, F j (p j) :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

private theorem prod_split {M : Type*} [CommMonoid M] (F : I → ℕ → M) (p : I → ℕ) (i : I) :
    ∏ j, F j (p j) = F i (p i) * ∏ j ∈ Finset.univ.erase i, F j (p j) :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

omit [Fintype I] in
private theorem update_pred_update_succ (p : I → ℕ) (i : I) :
    Function.update (Function.update p i (p i + 1)) i
        ((Function.update p i (p i + 1)) i - 1) = p := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    omega
  · simp only [Function.update_of_ne hj]

omit [Fintype I] in
private theorem update_succ_update_pred {q : I → ℕ} {i : I} (hi : q i ≠ 0) :
    Function.update (Function.update q i (q i - 1)) i
        ((Function.update q i (q i - 1)) i + 1) = q := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    omega
  · simp only [Function.update_of_ne hj]

/-! ## Pascal's rule for multinomial coefficients -/

/-- **Pascal's rule in multinomial form.**  Decrementing a nonzero coordinate of a multiplicity
vector of mass `r + 1` and summing the resulting multinomial coefficients returns the original
multinomial coefficient. -/
theorem multinomial_sum_update_pred {q : I → ℕ} {r : ℕ} (hq : ∑ i, q i = r + 1) :
    ∑ i ∈ Finset.univ.filter (fun i => q i ≠ 0),
        Nat.multinomial Finset.univ (Function.update q i (q i - 1))
      = Nat.multinomial Finset.univ q := by
  classical
  have hP : 0 < ∏ j, (q j).factorial :=
    Finset.prod_pos fun j _ => Nat.factorial_pos _
  have hkey : ∀ i ∈ Finset.univ.filter (fun i => q i ≠ 0),
      Nat.multinomial Finset.univ (Function.update q i (q i - 1)) * ∏ j, (q j).factorial
        = q i * r.factorial := by
    intro i hi
    have hqi : q i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hsum' : ∑ j, Function.update q i (q i - 1) j = r := by
      have h1 := sum_update_split (M := ℕ) (fun _ x => x) q i (q i - 1)
      have h2 := sum_split (M := ℕ) (fun _ x => x) q i
      omega
    have hprod : ∏ j, (q j).factorial
        = q i * ∏ j, (Function.update q i (q i - 1) j).factorial := by
      have h1 := prod_split (M := ℕ) (fun _ x => x.factorial) q i
      have h2 := prod_update_split (M := ℕ) (fun _ x => x.factorial) q i (q i - 1)
      have h3 : (q i).factorial = q i * (q i - 1).factorial := by
        obtain ⟨k, hk⟩ : ∃ k, q i = k + 1 := ⟨q i - 1, by omega⟩
        rw [hk, Nat.factorial_succ]
        simp
      rw [h1, h2, h3]
      ring
    have hspec := Nat.multinomial_spec (Finset.univ : Finset I)
      (Function.update q i (q i - 1))
    rw [hsum'] at hspec
    calc Nat.multinomial Finset.univ (Function.update q i (q i - 1)) * ∏ j, (q j).factorial
        = q i * ((∏ j, (Function.update q i (q i - 1) j).factorial) *
            Nat.multinomial Finset.univ (Function.update q i (q i - 1))) := by
          rw [hprod]; ring
      _ = q i * r.factorial := by rw [hspec]
  have hleft : (∑ i ∈ Finset.univ.filter (fun i => q i ≠ 0),
        Nat.multinomial Finset.univ (Function.update q i (q i - 1))) * ∏ j, (q j).factorial
      = (r + 1).factorial := by
    rw [Finset.sum_mul, Finset.sum_congr rfl hkey, ← Finset.sum_mul,
      Finset.sum_filter_ne_zero, hq, Nat.factorial_succ]
  have hright := Nat.multinomial_spec (Finset.univ : Finset I) q
  rw [hq] at hright
  refine Nat.eq_of_mul_eq_mul_right hP ?_
  rw [hleft, mul_comm]
  exact hright.symm

/-! ## The amplitude recursion -/

/-- Weighted sum of an arbitrary function over the replica multiplicity vectors of mass `r`. -/
noncomputable def replicaAmplitudeMoment (weight : I → ℝ) (r : ℕ) (Φ : (I → ℕ) → ℝ) : ℝ :=
  ∑ p ∈ Finset.univ.piAntidiag r, fidelityReplicaMultiplicityAmplitude weight p * Φ p

theorem replicaAmplitudeMoment_zero (weight : I → ℝ) (Φ : (I → ℕ) → ℝ) :
    replicaAmplitudeMoment weight 0 Φ = Φ 0 := by
  classical
  unfold replicaAmplitudeMoment
  rw [Finset.piAntidiag_zero, Finset.sum_singleton, fidelityReplicaMultiplicityAmplitude]
  simp [Nat.multinomial]

theorem replicaAmplitudeMoment_add (weight : I → ℝ) (r : ℕ) (Φ Ψ : (I → ℕ) → ℝ) :
    replicaAmplitudeMoment weight r (fun p => Φ p + Ψ p)
      = replicaAmplitudeMoment weight r Φ + replicaAmplitudeMoment weight r Ψ := by
  classical
  unfold replicaAmplitudeMoment
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem replicaAmplitudeMoment_const_mul (weight : I → ℝ) (r : ℕ) (c : ℝ) (Φ : (I → ℕ) → ℝ) :
    replicaAmplitudeMoment weight r (fun p => c * Φ p)
      = c * replicaAmplitudeMoment weight r Φ := by
  classical
  unfold replicaAmplitudeMoment
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- **The replica amplitude recursion.**  Every weighted sum over multiplicity vectors of mass
`r + 1` is the single level average of the corresponding sums of mass `r`, taken along the
coordinate that was incremented. -/
theorem replicaAmplitudeMoment_succ (weight : I → ℝ) (r : ℕ) (Φ : (I → ℕ) → ℝ) :
    replicaAmplitudeMoment weight (r + 1) Φ
      = ∑ i, weight i *
          replicaAmplitudeMoment weight r (fun p => Φ (Function.update p i (p i + 1))) := by
  classical
  unfold replicaAmplitudeMoment
  have hpush : ∀ i : I, weight i *
      (∑ p ∈ Finset.univ.piAntidiag r, fidelityReplicaMultiplicityAmplitude weight p *
        Φ (Function.update p i (p i + 1)))
      = ∑ p ∈ Finset.univ.piAntidiag r, weight i *
          (fidelityReplicaMultiplicityAmplitude weight p *
            Φ (Function.update p i (p i + 1))) := fun i => Finset.mul_sum _ _ _
  rw [Finset.sum_congr rfl fun i _ => hpush i]
  rw [Finset.sum_sigma' (Finset.univ : Finset I)
    (fun _ => Finset.univ.piAntidiag r)
    (fun i p => weight i * (fidelityReplicaMultiplicityAmplitude weight p *
      Φ (Function.update p i (p i + 1))))]
  -- reindex pairs `(coordinate, small vector)` as `(large vector, incremented coordinate)`
  have hbij : ∑ x ∈ (Finset.univ : Finset I).sigma (fun _ => Finset.univ.piAntidiag r),
      weight x.1 * (fidelityReplicaMultiplicityAmplitude weight x.2 *
        Φ (Function.update x.2 x.1 (x.2 x.1 + 1)))
      = ∑ y ∈ (Finset.univ.piAntidiag (r + 1)).sigma
          (fun q : I → ℕ => Finset.univ.filter (fun i => q i ≠ 0)),
        weight y.2 * (fidelityReplicaMultiplicityAmplitude weight
          (Function.update y.1 y.2 (y.1 y.2 - 1)) * Φ y.1) := by
    refine Finset.sum_nbij'
      (i := fun x => ⟨Function.update x.2 x.1 (x.2 x.1 + 1), x.1⟩)
      (j := fun y => ⟨y.2, Function.update y.1 y.2 (y.1 y.2 - 1)⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨i, p⟩ hx
      rw [Finset.mem_sigma] at hx
      have hp : ∑ j, p j = r := by
        have := (Finset.mem_piAntidiag.mp hx.2).1
        simpa using this
      have h1 := sum_update_split (M := ℕ) (fun _ x => x) p i (p i + 1)
      have h2 := sum_split (M := ℕ) (fun _ x => x) p i
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · show Function.update p i (p i + 1) ∈ Finset.univ.piAntidiag (r + 1)
        rw [Finset.mem_piAntidiag]
        refine ⟨?_, fun j _ => Finset.mem_univ j⟩
        show ∑ j, Function.update p i (p i + 1) j = r + 1
        omega
      · show i ∈ Finset.univ.filter (fun j => Function.update p i (p i + 1) j ≠ 0)
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ i, by simp⟩
    · rintro ⟨q, i⟩ hy
      rw [Finset.mem_sigma] at hy
      have hqi : q i ≠ 0 := (Finset.mem_filter.mp hy.2).2
      have hq : ∑ j, q j = r + 1 := by
        have := (Finset.mem_piAntidiag.mp hy.1).1
        simpa using this
      have h1 := sum_update_split (M := ℕ) (fun _ x => x) q i (q i - 1)
      have h2 := sum_split (M := ℕ) (fun _ x => x) q i
      refine Finset.mem_sigma.mpr ⟨Finset.mem_univ i, ?_⟩
      show Function.update q i (q i - 1) ∈ Finset.univ.piAntidiag r
      rw [Finset.mem_piAntidiag]
      refine ⟨?_, fun j _ => Finset.mem_univ j⟩
      show ∑ j, Function.update q i (q i - 1) j = r
      omega
    · rintro ⟨i, p⟩ _
      dsimp only
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
      exact update_pred_update_succ p i
    · rintro ⟨q, i⟩ hy
      rw [Finset.mem_sigma] at hy
      dsimp only at hy
      have hqi : q i ≠ 0 := (Finset.mem_filter.mp hy.2).2
      dsimp only
      simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
      exact update_succ_update_pred hqi
    · rintro ⟨i, p⟩ _
      dsimp only
      rw [update_pred_update_succ p i]
  have hsig : ∑ y ∈ (Finset.univ.piAntidiag (r + 1)).sigma
        (fun q : I → ℕ => Finset.univ.filter (fun i => q i ≠ 0)),
      weight y.2 * (fidelityReplicaMultiplicityAmplitude weight
        (Function.update y.1 y.2 (y.1 y.2 - 1)) * Φ y.1)
      = ∑ q ∈ Finset.univ.piAntidiag (r + 1),
          ∑ i ∈ Finset.univ.filter (fun i => q i ≠ 0),
            weight i * (fidelityReplicaMultiplicityAmplitude weight
              (Function.update q i (q i - 1)) * Φ q) :=
    (Finset.sum_sigma' (Finset.univ.piAntidiag (r + 1))
      (fun q : I → ℕ => Finset.univ.filter (fun i => q i ≠ 0))
      (fun q i => weight i * (fidelityReplicaMultiplicityAmplitude weight
        (Function.update q i (q i - 1)) * Φ q))).symm
  rw [hbij, hsig]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqsum : ∑ j, q j = r + 1 := by
    have := (Finset.mem_piAntidiag.mp hq).1
    simpa using this
  have hinner : ∀ i ∈ Finset.univ.filter (fun i => q i ≠ 0),
      weight i * (fidelityReplicaMultiplicityAmplitude weight
          (Function.update q i (q i - 1)) * Φ q)
        = (Nat.multinomial Finset.univ (Function.update q i (q i - 1)) : ℝ) *
            ((∏ j, weight j ^ q j) * Φ q) := by
    intro i hi
    have hqi : q i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hpow : weight i * ∏ j, weight j ^ (Function.update q i (q i - 1) j)
        = ∏ j, weight j ^ q j := by
      have h1 := prod_split (M := ℝ) (fun j x => weight j ^ x) q i
      have h2 := prod_update_split (M := ℝ) (fun j x => weight j ^ x) q i (q i - 1)
      have h3 : weight i * weight i ^ (q i - 1) = weight i ^ q i := by
        obtain ⟨k, hk⟩ : ∃ k, q i = k + 1 := ⟨q i - 1, by omega⟩
        rw [hk]
        simp [pow_succ]
        ring
      rw [h1, h2, ← mul_assoc, h3]
    rw [fidelityReplicaMultiplicityAmplitude]
    calc weight i * ((Nat.multinomial Finset.univ (Function.update q i (q i - 1)) : ℝ) *
            (∏ j, weight j ^ (Function.update q i (q i - 1) j)) * Φ q)
        = (Nat.multinomial Finset.univ (Function.update q i (q i - 1)) : ℝ) *
            ((weight i * ∏ j, weight j ^ (Function.update q i (q i - 1) j)) * Φ q) := by ring
      _ = (Nat.multinomial Finset.univ (Function.update q i (q i - 1)) : ℝ) *
            ((∏ j, weight j ^ q j) * Φ q) := by rw [hpow]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, ← Nat.cast_sum,
    multinomial_sum_update_pred hqsum, fidelityReplicaMultiplicityAmplitude]
  ring

/-! ## Moments of the replica energy -/

theorem replicaAmplitudeMoment_one {weight : I → ℝ} (hw : ∑ i, weight i = 1) (r : ℕ) :
    replicaAmplitudeMoment weight r (fun _ => 1) = 1 := by
  induction r with
  | zero => rw [replicaAmplitudeMoment_zero]
  | succ r ih =>
      rw [replicaAmplitudeMoment_succ]
      simp only [ih]
      simpa using hw

theorem replicaMultiplicityEnergy_update_succ (energy : I → ℝ) (p : I → ℕ) (i : I) :
    replicaMultiplicityEnergy energy (Function.update p i (p i + 1))
      = replicaMultiplicityEnergy energy p + energy i := by
  unfold replicaMultiplicityEnergy
  have h1 := sum_update_split (M := ℝ) (fun j x => (x : ℝ) * energy j) p i (p i + 1)
  have h2 := sum_split (M := ℝ) (fun j x => (x : ℝ) * energy j) p i
  rw [h1, h2]
  push_cast
  ring

/-- **The mean replica energy.**  At replica order `r` the mean energy is `r` times the single
level mean. -/
theorem replicaAmplitudeMoment_energy {weight : I → ℝ} (hw : ∑ i, weight i = 1)
    (energy : I → ℝ) (r : ℕ) :
    replicaAmplitudeMoment weight r (replicaMultiplicityEnergy energy)
      = r * ∑ i, weight i * energy i := by
  induction r with
  | zero =>
      rw [replicaAmplitudeMoment_zero]
      unfold replicaMultiplicityEnergy
      simp
  | succ r ih =>
      rw [replicaAmplitudeMoment_succ]
      have hstep : ∀ i : I,
          replicaAmplitudeMoment weight r
              (fun p => replicaMultiplicityEnergy energy (Function.update p i (p i + 1)))
            = (r : ℝ) * (∑ j, weight j * energy j) + energy i := by
        intro i
        have hrw : (fun p : I → ℕ =>
            replicaMultiplicityEnergy energy (Function.update p i (p i + 1)))
            = fun p => replicaMultiplicityEnergy energy p + energy i * 1 := by
          funext p
          rw [replicaMultiplicityEnergy_update_succ]
          ring
        rw [hrw, replicaAmplitudeMoment_add, replicaAmplitudeMoment_const_mul,
          replicaAmplitudeMoment_one hw, ih]
        ring
      simp only [hstep]
      have hexp : ∑ i, weight i * ((r : ℝ) * (∑ j, weight j * energy j) + energy i)
          = (∑ i, weight i) * ((r : ℝ) * ∑ j, weight j * energy j)
            + ∑ i, weight i * energy i := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hexp, hw]
      push_cast
      ring

/-- **The second moment of the replica energy.** -/
theorem replicaAmplitudeMoment_energy_sq {weight : I → ℝ} (hw : ∑ i, weight i = 1)
    (energy : I → ℝ) (r : ℕ) :
    replicaAmplitudeMoment weight r (fun p => replicaMultiplicityEnergy energy p ^ (2 : ℕ))
      = r * (∑ i, weight i * energy i ^ (2 : ℕ))
        + (r : ℝ) * ((r : ℝ) - 1) * (∑ i, weight i * energy i) ^ (2 : ℕ) := by
  induction r with
  | zero =>
      rw [replicaAmplitudeMoment_zero]
      unfold replicaMultiplicityEnergy
      simp
  | succ r ih =>
      rw [replicaAmplitudeMoment_succ]
      have hstep : ∀ i : I,
          replicaAmplitudeMoment weight r
              (fun p => replicaMultiplicityEnergy energy
                (Function.update p i (p i + 1)) ^ (2 : ℕ))
            = ((r : ℝ) * (∑ j, weight j * energy j ^ (2 : ℕ))
                + (r : ℝ) * ((r : ℝ) - 1) * (∑ j, weight j * energy j) ^ (2 : ℕ))
              + 2 * energy i * ((r : ℝ) * ∑ j, weight j * energy j)
              + energy i ^ (2 : ℕ) := by
        intro i
        have hrw : (fun p : I → ℕ =>
            replicaMultiplicityEnergy energy (Function.update p i (p i + 1)) ^ (2 : ℕ))
            = fun p => (replicaMultiplicityEnergy energy p ^ (2 : ℕ)
                + (2 * energy i) * replicaMultiplicityEnergy energy p)
              + (energy i ^ (2 : ℕ)) * 1 := by
          funext p
          rw [replicaMultiplicityEnergy_update_succ]
          ring
        rw [hrw, replicaAmplitudeMoment_add, replicaAmplitudeMoment_add,
          replicaAmplitudeMoment_const_mul, replicaAmplitudeMoment_const_mul,
          replicaAmplitudeMoment_one hw, replicaAmplitudeMoment_energy hw, ih]
        ring
      have hexp : ∀ A B : ℝ, ∑ i, weight i * (A + 2 * energy i * B + energy i ^ (2 : ℕ))
          = (∑ i, weight i) * A + 2 * B * (∑ i, weight i * energy i)
            + ∑ i, weight i * energy i ^ (2 : ℕ) := by
        intro A B
        have hterm : ∀ i : I, weight i * (A + 2 * energy i * B + energy i ^ (2 : ℕ))
            = weight i * A + (2 * B) * (weight i * energy i) + weight i * energy i ^ (2 : ℕ) :=
          fun i => by ring
        rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
          Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      simp only [hstep]
      rw [hexp, hw]
      push_cast
      ring

/-- **The replica energy variance.**  The variance of the order-`r` replica energy about `r` times
the single level mean is exactly `r` times the single level variance.  This is the exact finite
form of the additivity of variance under independent sampling. -/
theorem replicaAmplitudeMoment_energy_variance {weight : I → ℝ} (hw : ∑ i, weight i = 1)
    (energy : I → ℝ) (r : ℕ) :
    replicaAmplitudeMoment weight r
        (fun p => (replicaMultiplicityEnergy energy p
          - r * ∑ i, weight i * energy i) ^ (2 : ℕ))
      = r * ∑ i, weight i * (energy i - ∑ j, weight j * energy j) ^ (2 : ℕ) := by
  have hmean : ∑ i, weight i * (energy i - ∑ j, weight j * energy j) ^ (2 : ℕ)
      = (∑ i, weight i * energy i ^ (2 : ℕ)) - (∑ i, weight i * energy i) ^ (2 : ℕ) := by
    have hexpand : ∀ i : I, weight i * (energy i - ∑ j, weight j * energy j) ^ (2 : ℕ)
        = weight i * energy i ^ (2 : ℕ)
          - 2 * (∑ j, weight j * energy j) * (weight i * energy i)
          + (∑ j, weight j * energy j) ^ (2 : ℕ) * weight i := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => hexpand i]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw]
    ring
  have hrw : (fun p : I → ℕ =>
      (replicaMultiplicityEnergy energy p - r * ∑ i, weight i * energy i) ^ (2 : ℕ))
      = fun p => (replicaMultiplicityEnergy energy p ^ (2 : ℕ)
          + (-2 * ((r : ℝ) * ∑ i, weight i * energy i)) * replicaMultiplicityEnergy energy p)
        + (((r : ℝ) * ∑ i, weight i * energy i) ^ (2 : ℕ)) * 1 := by
    funext p
    ring
  rw [hrw, replicaAmplitudeMoment_add, replicaAmplitudeMoment_add,
    replicaAmplitudeMoment_const_mul, replicaAmplitudeMoment_const_mul,
    replicaAmplitudeMoment_one hw, replicaAmplitudeMoment_energy hw,
    replicaAmplitudeMoment_energy_sq hw, hmean]
  ring

/-- The replica amplitudes of a probability weighting have total mass one. -/
theorem replicaAmplitude_total_mass {weight : I → ℝ} (hw : ∑ i, weight i = 1) (r : ℕ) :
    ∑ p ∈ Finset.univ.piAntidiag r, fidelityReplicaMultiplicityAmplitude weight p = 1 := by
  classical
  have h := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset I) weight r
  rw [hw, one_pow] at h
  rw [h]
  exact Finset.sum_congr rfl fun p _ => rfl

omit [DecidableEq I] in
/-- The replica amplitude of a nonnegative weighting is nonnegative. -/
theorem fidelityReplicaMultiplicityAmplitude_nonneg {weight : I → ℝ}
    (hw : ∀ i, 0 ≤ weight i) (p : I → ℕ) :
    0 ≤ fidelityReplicaMultiplicityAmplitude weight p := by
  rw [fidelityReplicaMultiplicityAmplitude]
  exact mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg fun i _ => pow_nonneg (hw i) _)

end GaloisForLFunctions.HTGeometry
