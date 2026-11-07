import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheDualOfTheRateIsAFakePrimeMeasure
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheHalfScaleOfTheRate
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# The extremal fake prime measure

Fix an alphabet `[2, K]` and a finite target set `S` inside one period, for instance a window `[1, B)`. The best slope is a
finite linear program: minimize `Σ q_k log k` over real weights with `f = Σ q_k (r mod k) ≥ 0` on a period and `f ≥ 1` on `S`. Its dual
maximizes the mass on `S` of a nonnegative measure on residues with the moments `Σ u(r) (r mod k) = log k`.

**Strong duality holds, and the dual optimum is attained**: for each `K` and `B` there is an extremal fake prime
measure `u`, supported on one period, whose window mass is the exact value of the program. Integer producers
approach this value, because the feasible set is cut out by rational inequalities and has interior directions.
So the best normalized slope at window `B` equals `mass(u)/(1 − 1/B)`. This is the fake prime measure closest
to the true one, in the only sense the producers can read: no other consistent measure has larger window mass.

The excess of a producer is the integral of its slack against any fake prime measure, so an extremal measure
lives on the set where the multiplicity sits at its lower bound.

**How close it is.** The window mass of the true measure is `1 − 1/B`. At the best window the extremal mass is within a factor
`1 + exp(−(log K)^α)` of it, for `α < 3/5`, and at every window it exceeds it by a factor at least `1 + c/(√K (1 + log K))`. So a fake prime
measure of level `K` can be told apart from the truth, and only by very little.

The proof separates the point `(log k, value)` from the cone of attainable moments. The cone is closed because
the moments control the mass: every residue off the period has a letter that does not divide it.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The common period of the letters `[2, K]`. -/
def lcmUpTo (K : ℕ) : ℕ := (Icc 2 K).lcm id

theorem dvd_lcmUpTo {K k : ℕ} (hk : k ∈ Icc 2 K) : k ∣ lcmUpTo K := Finset.dvd_lcm (f := id) hk

theorem lcmUpTo_pos (K : ℕ) : 0 < lcmUpTo K := by
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [lcmUpTo, Finset.lcm_eq_zero_iff] at h
  obtain ⟨k, hk, hk0⟩ := h
  have h2 := (mem_Icc.mp (mem_coe.mp hk)).1
  simp only [id] at hk0
  omega

/-- The sawtooth sum of real weights on the letters `[2, K]`. -/
def saw (q : ℕ → ℝ) (K r : ℕ) : ℝ := ∑ k ∈ Icc 2 K, q k * ((r % k : ℕ) : ℝ)

/-- The cost `Σ q_k log k` of the weights, the slope of the stencil they define. -/
def objective (q : ℕ → ℝ) (K : ℕ) : ℝ := ∑ k ∈ Icc 2 K, q k * Real.log k

theorem saw_mod (q : ℕ → ℝ) (K r : ℕ) : saw q K (r % lcmUpTo K) = saw q K r :=
  sum_congr rfl fun k hk => by rw [Nat.mod_mod_of_dvd _ (dvd_lcmUpTo hk)]

theorem saw_zero (q : ℕ → ℝ) (K : ℕ) : saw q K 0 = 0 := by
  simp [saw]

/-- A residue off the period has a letter that does not divide it. -/
theorem exists_letter_mod {K r : ℕ} (h1 : 1 ≤ r) (h2 : r < lcmUpTo K) : ∃ k ∈ Icc 2 K, 1 ≤ r % k := by
  by_contra hall
  push Not at hall
  have hdvd : lcmUpTo K ∣ r := Finset.lcm_dvd fun k hk =>
    Nat.dvd_of_mod_eq_zero (Nat.lt_one_iff.mp (hall k hk))
  have := Nat.le_of_dvd (by omega) hdvd
  omega

theorem one_le_saw_one {K r : ℕ} (h1 : 1 ≤ r) (h2 : r < lcmUpTo K) : 1 ≤ saw (fun _ => 1) K r := by
  obtain ⟨k, hk, hkr⟩ := exists_letter_mod h1 h2
  have hle := single_le_sum (f := fun k => (1 : ℝ) * ((r % k : ℕ) : ℝ))
    (fun i _ => by positivity) hk
  have hkr' : (1 : ℝ) ≤ ((r % k : ℕ) : ℝ) := by exact_mod_cast hkr
  simp only [one_mul] at hle
  simp only [saw, one_mul]
  linarith

/-- The feasible weights of the program with target `S`: a nonnegative sawtooth sum, at least `1` on `S`. -/
structure IsFeasible (K : ℕ) (S : Finset ℕ) (q : ℕ → ℝ) : Prop where
  nonneg : ∀ r, 1 ≤ r → r < lcmUpTo K → 0 ≤ saw q K r
  target : ∀ r ∈ S, 1 ≤ saw q K r

/-- A balanced stencil whose multiplicity is nonnegative and at least `m ≥ 1` on `S`: a producer with an arbitrary target in
place of a window. -/
structure IsShapeProducer (c : ℕ →₀ ℤ) (m : ℕ) (S : Finset ℕ) : Prop where
  zero : c 0 = 0
  balanced : IsBalanced c
  nonneg : ∀ r : ℕ, 0 ≤ stepWeight c r
  one_le_m : 1 ≤ m
  target : ∀ r ∈ S, (m : ℤ) ≤ stepWeight c r

/-- The mass of a measure on `r = j + 1` on a target set. -/
def targetMass (u : ℕ → ℝ) (S : Finset ℕ) : ℝ := ∑ r ∈ S, u (r - 1)

theorem targetMass_Ico (u : ℕ → ℝ) (B : ℕ) : targetMass u (Ico 1 B) = ∑ j ∈ range (B - 1), u j := by
  rw [targetMass, sum_Ico_eq_sum_range]
  refine sum_congr rfl fun j _ => ?_
  congr 1
  omega

private lemma mem_window {K B : ℕ} (hBL : B ≤ lcmUpTo K) : ∀ r ∈ Ico 1 B, 1 ≤ r ∧ r < lcmUpTo K :=
  fun r hr => ⟨(mem_Ico.mp hr).1, lt_of_lt_of_le (mem_Ico.mp hr).2 hBL⟩

theorem IsFeasible.saw_nonneg {K : ℕ} {S : Finset ℕ} {q : ℕ → ℝ} (hF : IsFeasible K S q) (r : ℕ) :
    0 ≤ saw q K r := by
  rw [← saw_mod]
  rcases Nat.eq_zero_or_pos (r % lcmUpTo K) with h | h
  · rw [h, saw_zero]
  · exact hF.nonneg _ h (Nat.mod_lt _ (lcmUpTo_pos K))

theorem isFeasible_const {K : ℕ} {S : Finset ℕ} (hS : ∀ r ∈ S, 1 ≤ r ∧ r < lcmUpTo K) :
    IsFeasible K S fun _ => 1 :=
  ⟨fun r h1 h2 => le_trans zero_le_one (one_le_saw_one h1 h2),
    fun r hr => one_le_saw_one (hS r hr).1 (hS r hr).2⟩

/-- **Weak duality for real weights.** A fake prime measure computes the cost as an integral of the sawtooth. -/
theorem IsFakePrimeMeasure.hasSum_saw {K : ℕ} {u : ℕ → ℝ} (hu : IsFakePrimeMeasure K u) (q : ℕ → ℝ) :
    HasSum (fun j => u j * saw q K (j + 1)) (objective q K) := by
  have hfun : (fun j => u j * saw q K (j + 1)) =
      fun j => ∑ k ∈ Icc 2 K, q k * (u j * (((j + 1) % k : ℕ) : ℝ)) := by
    funext j
    rw [saw, mul_sum]
    exact sum_congr rfl fun k _ => by ring
  rw [hfun, objective]
  refine hasSum_sum fun k hk => ?_
  have hk' := mem_Icc.mp hk
  exact (hu.moment k (mem_Icc.mpr ⟨by omega, hk'.2⟩)).mul_left (q k)

theorem IsFeasible.objective_nonneg {K : ℕ} {S : Finset ℕ} {q : ℕ → ℝ} (hF : IsFeasible K S q) :
    0 ≤ objective q K := by
  have h := (isFakePrimeMeasure_pronic K).hasSum_saw q
  exact h.nonneg fun j => mul_nonneg (by positivity) (hF.saw_nonneg _)

/-- A fake prime measure bounds the cost below by its mass on the target. -/
theorem IsFeasible.mass_le {K : ℕ} {S : Finset ℕ} {q : ℕ → ℝ} (hF : IsFeasible K S q) (hS : ∀ r ∈ S, 1 ≤ r)
    {u : ℕ → ℝ} (hu : IsFakePrimeMeasure K u) : targetMass u S ≤ objective q K := by
  classical
  have hterm : ∀ j, 0 ≤ u j * saw q K (j + 1) := fun j => mul_nonneg (hu.nonneg j) (hF.saw_nonneg _)
  have hinj : Set.InjOn (fun r : ℕ => r - 1) (S : Set ℕ) := by
    intro a ha b hb hab
    have h1 := hS a ha
    have h2 := hS b hb
    simp only at hab
    omega
  have himg : targetMass u S = ∑ j ∈ S.image (fun r => r - 1), u j := by
    rw [sum_image hinj]
    rfl
  rw [himg]
  refine le_trans ?_ (sum_le_hasSum (S.image fun r => r - 1) (fun j _ => hterm j) (hu.hasSum_saw q))
  refine sum_le_sum fun j hj => ?_
  obtain ⟨r, hr, rfl⟩ := mem_image.mp hj
  have hr1 := hS r hr
  have e : r - 1 + 1 = r := by omega
  rw [e]
  calc u (r - 1) = u (r - 1) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hF.target r hr) (hu.nonneg _)

/-- The value of the program with target `S`. -/
def lpValue (K : ℕ) (S : Finset ℕ) : ℝ := sInf {x | ∃ q, IsFeasible K S q ∧ objective q K = x}

private lemma lpValue_bdd (K : ℕ) (S : Finset ℕ) : BddBelow {x | ∃ q, IsFeasible K S q ∧ objective q K = x} :=
  ⟨0, by
    rintro x ⟨q, hq, rfl⟩
    exact hq.objective_nonneg⟩

theorem lpValue_le {K : ℕ} {S : Finset ℕ} {q : ℕ → ℝ} (hF : IsFeasible K S q) : lpValue K S ≤ objective q K :=
  csInf_le (lpValue_bdd K S) ⟨q, hF, rfl⟩

private lemma sum_Icc_two_eq (g : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Icc 2 K, g k = ∑ i : Fin (K - 1), g ((i : ℕ) + 2) := by
  have hset : Icc 2 K = Ico 2 (K + 1) := by
    ext x
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hset, sum_Ico_eq_sum_range, Fin.sum_univ_eq_sum_range (fun i => g (i + 2)) (K - 1)]
  have hn : K + 1 - 2 = K - 1 := by omega
  rw [hn]
  exact sum_congr rfl fun i _ => by rw [add_comm]

/-- The moment map of the program: `(u, t) ↦ (Σ u(r) (r mod k), mass on the target − t)`. -/
private def phi (K : ℕ) (S : Finset ℕ) (z : (Fin (lcmUpTo K - 1) → ℝ) × ℝ) : (Fin (K - 1) → ℝ) × ℝ :=
  (fun i : Fin (K - 1) => ∑ j : Fin (lcmUpTo K - 1), z.1 j * ((((j : ℕ) + 1) % ((i : ℕ) + 2) : ℕ) : ℝ),
    (∑ j : Fin (lcmUpTo K - 1), (if (j : ℕ) + 1 ∈ S then (1 : ℝ) else 0) * z.1 j) - z.2)

private lemma phi_add (K : ℕ) (S : Finset ℕ) (z w : (Fin (lcmUpTo K - 1) → ℝ) × ℝ) :
    phi K S (z + w) = phi K S z + phi K S w := by
  refine Prod.ext (funext fun i => ?_) ?_
  · simp only [phi, Prod.fst_add, Pi.add_apply, add_mul, sum_add_distrib]
  · simp only [phi, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, sum_add_distrib]
    ring

private lemma phi_smul (K : ℕ) (S : Finset ℕ) (a : ℝ) (z : (Fin (lcmUpTo K - 1) → ℝ) × ℝ) :
    phi K S (a • z) = a • phi K S z := by
  refine Prod.ext (funext fun i => ?_) ?_
  · simp only [phi, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, mul_sum, mul_assoc]
  · simp only [phi, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [mul_sub, mul_sum]
    congr 1
    exact sum_congr rfl fun j _ => by ring

private lemma phi_continuous (K : ℕ) (S : Finset ℕ) : Continuous (phi K S) := by
  unfold phi
  fun_prop

/-- The cone of attainable moments. -/
private def momentCone (K : ℕ) (S : Finset ℕ) : Set ((Fin (K - 1) → ℝ) × ℝ) :=
  phi K S '' {z | 0 ≤ z.1 ∧ 0 ≤ z.2}

private lemma momentCone_convex (K : ℕ) (S : Finset ℕ) : Convex ℝ (momentCone K S) := by
  rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩ _ ⟨w, ⟨hw1, hw2⟩, rfl⟩ a b ha hb _
  refine ⟨a • z + b • w, ⟨?_, ?_⟩, ?_⟩
  · exact add_nonneg (smul_nonneg ha hz1) (smul_nonneg hb hw1)
  · exact add_nonneg (mul_nonneg ha hz2) (mul_nonneg hb hw2)
  · rw [phi_add, phi_smul, phi_smul]

/-- Each residue off the period is seen by some moment, so the moments bound the measure. -/
private lemma le_sum_moments (K : ℕ) (S : Finset ℕ) {u : Fin (lcmUpTo K - 1) → ℝ} (hu : 0 ≤ u)
    (j : Fin (lcmUpTo K - 1)) : u j ≤ ∑ i, (phi K S (u, 0)).1 i := by
  have hj := j.2
  obtain ⟨k, hk, hkr⟩ := exists_letter_mod (K := K) (r := (j : ℕ) + 1) (by omega) (by omega)
  have hk' := mem_Icc.mp hk
  have hi : k - 2 < K - 1 := by omega
  have hterm : ∀ i : Fin (K - 1), 0 ≤ (phi K S (u, 0)).1 i := by
    intro i
    change 0 ≤ ∑ j : Fin (lcmUpTo K - 1), u j * ((((j : ℕ) + 1) % ((i : ℕ) + 2) : ℕ) : ℝ)
    exact sum_nonneg fun j _ => mul_nonneg (hu j) (Nat.cast_nonneg _)
  have h1 : (phi K S (u, 0)).1 ⟨k - 2, hi⟩ ≤ ∑ i, (phi K S (u, 0)).1 i :=
    single_le_sum (fun i _ => hterm i) (mem_univ _)
  have h2 : u j ≤ (phi K S (u, 0)).1 ⟨k - 2, hi⟩ := by
    have hsingle := single_le_sum
      (f := fun j' : Fin (lcmUpTo K - 1) =>
        u j' * ((((j' : ℕ) + 1) % ((k - 2) + 2) : ℕ) : ℝ))
      (fun j' _ => mul_nonneg (hu j') (Nat.cast_nonneg _)) (mem_univ j)
    have hkk : k - 2 + 2 = k := by omega
    have hcast : (1 : ℝ) ≤ ((((j : ℕ) + 1) % ((k - 2) + 2) : ℕ) : ℝ) := by
      rw [hkk]
      exact_mod_cast hkr
    calc u j = u j * 1 := (mul_one _).symm
      _ ≤ u j * ((((j : ℕ) + 1) % ((k - 2) + 2) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hcast (hu j)
      _ ≤ ∑ j' : Fin (lcmUpTo K - 1), u j' * ((((j' : ℕ) + 1) % ((k - 2) + 2) : ℕ) : ℝ) := hsingle
  exact h2.trans h1

/-- **The cone of moments is closed.** -/
private lemma momentCone_closed (K : ℕ) (S : Finset ℕ) : IsClosed (momentCone K S) := by
  refine IsSeqClosed.isClosed fun x a hx hlim => ?_
  choose z hz hphi using hx
  have hs : Tendsto (fun n => ∑ i, (x n).1 i) atTop (𝓝 (∑ i, a.1 i)) :=
    tendsto_finsetSum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).tendsto a |>.comp hlim
  have ht : Tendsto (fun n => -(x n).2) atTop (𝓝 (-a.2)) :=
    (continuous_snd.neg.tendsto a).comp hlim
  obtain ⟨C₁, hC₁⟩ := hs.bddAbove_range
  obtain ⟨C₂, hC₂⟩ := ht.bddAbove_range
  have hs1 : ∀ n, ∑ i, (x n).1 i ≤ C₁ := fun n => hC₁ ⟨n, rfl⟩
  have ht1 : ∀ n, -(x n).2 ≤ C₂ := fun n => hC₂ ⟨n, rfl⟩
  -- The measures are uniformly bounded by the first moments.
  have hu : ∀ n j, (z n).1 j ≤ C₁ := by
    intro n j
    have h1 := le_sum_moments K S (hz n).1 j
    have hfst : (phi K S ((z n).1, 0)).1 = (phi K S (z n)).1 := rfl
    rw [hfst, hphi n] at h1
    exact h1.trans (hs1 n)
  set N : ℝ := ((lcmUpTo K - 1 : ℕ) : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hC₁0 : ∀ n, 0 ≤ C₁ → ∑ j : Fin (lcmUpTo K - 1), (if (j : ℕ) + 1 ∈ S then (1 : ℝ) else 0) * (z n).1 j ≤ N * C₁ := by
    intro n _
    calc ∑ j : Fin (lcmUpTo K - 1), (if (j : ℕ) + 1 ∈ S then (1 : ℝ) else 0) * (z n).1 j
        ≤ ∑ _j : Fin (lcmUpTo K - 1), C₁ := by
          refine sum_le_sum fun j _ => ?_
          have h0 := (hz n).1 j
          have h1 := hu n j
          split_ifs
          · linarith
          · by_contra hneg
            have : C₁ < 0 := by linarith
            linarith
      _ = N * C₁ := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hC₁nn : 0 ≤ C₁ ∨ IsEmpty (Fin (lcmUpTo K - 1)) := by
    by_cases he : IsEmpty (Fin (lcmUpTo K - 1))
    · exact Or.inr he
    · left
      rw [not_isEmpty_iff] at he
      obtain ⟨j⟩ := he
      exact ((hz 0).1 j).trans (hu 0 j)
  set C₃ : ℝ := N * |C₁| + C₂ with hC₃
  have htn : ∀ n, (z n).2 ≤ C₃ := by
    intro n
    have hsnd : (phi K S (z n)).2 = (∑ j : Fin (lcmUpTo K - 1), (if (j : ℕ) + 1 ∈ S then (1 : ℝ) else 0) * (z n).1 j) -
        (z n).2 := rfl
    rw [hphi n] at hsnd
    have h1 := ht1 n
    have h2 : ∑ j : Fin (lcmUpTo K - 1), (if (j : ℕ) + 1 ∈ S then (1 : ℝ) else 0) * (z n).1 j ≤ N * |C₁| := by
      refine le_trans (sum_le_sum (g := fun _ => |C₁|) fun j _ => ?_) ?_
      · have h0 := (hz n).1 j
        have h3 := hu n j
        have h4 := le_abs_self C₁
        split_ifs
        · linarith
        · have h5 := abs_nonneg C₁
          linarith
      · rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have hcompact : IsCompact (Set.Icc (0 : Fin (lcmUpTo K - 1) → ℝ) (fun _ => C₁) ×ˢ Set.Icc (0 : ℝ) C₃) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨w, hw, φ, hφ, hzlim⟩ := hcompact.tendsto_subseq (x := z) fun n =>
    ⟨⟨(hz n).1, fun j => hu n j⟩, ⟨(hz n).2, htn n⟩⟩
  have hlim1 : Tendsto (fun n => phi K S (z (φ n))) atTop (𝓝 (phi K S w)) :=
    ((phi_continuous K S).tendsto w).comp hzlim
  have hlim2 : Tendsto (fun n => x (φ n)) atTop (𝓝 a) := hlim.comp hφ.tendsto_atTop
  have heq : phi K S w = a := by
    refine tendsto_nhds_unique hlim1 ?_
    simpa only [hphi] using hlim2
  exact ⟨w, ⟨hw.1.1, hw.2.1⟩, heq⟩

private lemma phi_zero (K : ℕ) (S : Finset ℕ) : phi K S 0 = 0 := by
  have h := phi_smul K S 0 0
  simpa using h

/-- A continuous functional on the target is a weighted sum of coordinates. -/
private lemma dual_apply {n : ℕ} (f : StrongDual ℝ ((Fin n → ℝ) × ℝ)) (x : Fin n → ℝ) (c : ℝ) :
    f (x, c) = ∑ i, x i * f (Pi.single i 1, 0) + c * f (0, 1) := by
  have hdec : (x, c) = ∑ i, x i • ((Pi.single i 1 : Fin n → ℝ), (0 : ℝ)) +
      c • ((0 : Fin n → ℝ), (1 : ℝ)) := by
    refine Prod.ext ?_ ?_
    · funext i'
      simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sum, Pi.add_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, add_zero]
      simp [Pi.single_apply]
    · simp [Prod.snd_sum]
  conv_lhs => rw [hdec]
  rw [map_add, map_sum, map_smul, smul_eq_mul]
  simp only [map_smul, smul_eq_mul]

/-- **Strong duality.** The point `(log k, value)` is attained by a nonnegative measure and slack. -/
private lemma exists_dual_point {K : ℕ} {S : Finset ℕ} (hS : ∀ r ∈ S, 1 ≤ r ∧ r < lcmUpTo K) :
    ((fun i : Fin (K - 1) => Real.log ((i : ℕ) + 2 : ℕ)), lpValue K S) ∈ momentCone K S := by
  by_contra hnot
  obtain ⟨f, α, hf, hα⟩ := geometric_hahn_banach_closed_point (momentCone_convex K S)
    (momentCone_closed K S) hnot
  have h0 : (0 : (Fin (K - 1) → ℝ) × ℝ) ∈ momentCone K S :=
    ⟨0, ⟨le_rfl, le_rfl⟩, phi_zero K S⟩
  have hαpos : 0 < α := by
    have := hf 0 h0
    rwa [map_zero] at this
  -- The functional is nonpositive on the cone, since the cone is scale invariant.
  have hneg : ∀ z : (Fin (lcmUpTo K - 1) → ℝ) × ℝ, 0 ≤ z.1 → 0 ≤ z.2 → f (phi K S z) ≤ 0 := by
    intro z hz1 hz2
    by_contra hpos
    push Not at hpos
    set l := α / f (phi K S z) with hl
    have hl0 : 0 ≤ l := by positivity
    have hmem : phi K S (l • z) ∈ momentCone K S :=
      ⟨l • z, ⟨smul_nonneg hl0 hz1, mul_nonneg hl0 hz2⟩, rfl⟩
    have hlt := hf _ hmem
    rw [phi_smul, map_smul, smul_eq_mul, hl, div_mul_cancel₀ _ hpos.ne'] at hlt
    exact lt_irrefl _ hlt
  set y : Fin (K - 1) → ℝ := fun i => f (Pi.single i 1, 0) with hy
  set τ : ℝ := f (0, 1) with hτ
  have hdual : ∀ x c, f (x, c) = ∑ i, x i * y i + c * τ := fun x c => dual_apply f x c
  have hτ0 : 0 ≤ τ := by
    have h := hneg ((0 : Fin (lcmUpTo K - 1) → ℝ), (1 : ℝ)) le_rfl zero_le_one
    have hval : phi K S ((0 : Fin (lcmUpTo K - 1) → ℝ), (1 : ℝ)) = (0, -1) := by
      refine Prod.ext (funext fun i => ?_) ?_ <;> simp [phi]
    rw [hval, hdual] at h
    simp only [Pi.zero_apply, zero_mul, sum_const_zero, zero_add, neg_mul, one_mul] at h
    linarith
  -- The weights read off the functional.
  set q : ℕ → ℝ := fun k => if h : k - 2 < K - 1 then -y ⟨k - 2, h⟩ else 0 with hq
  have hqi : ∀ i : Fin (K - 1), q ((i : ℕ) + 2) = -y i := by
    intro i
    have hi : (i : ℕ) + 2 - 2 < K - 1 := by simpa using i.2
    have hfin : (⟨(i : ℕ) + 2 - 2, hi⟩ : Fin (K - 1)) = i := Fin.ext (by simp)
    simp only [hq, dif_pos hi, hfin]
  have hsaw : ∀ r, saw q K r = -∑ i : Fin (K - 1), ((r % ((i : ℕ) + 2) : ℕ) : ℝ) * y i := by
    intro r
    rw [saw, sum_Icc_two_eq, ← sum_neg_distrib]
    exact sum_congr rfl fun i _ => by rw [hqi]; ring
  have hobj : objective q K = -∑ i : Fin (K - 1), Real.log ((i : ℕ) + 2 : ℕ) * y i := by
    rw [objective, sum_Icc_two_eq, ← sum_neg_distrib]
    exact sum_congr rfl fun i _ => by rw [hqi]; ring
  -- Each residue gives one inequality.
  have hres : ∀ r, 1 ≤ r → r < lcmUpTo K → (if r ∈ S then τ else 0) ≤ saw q K r := by
    intro r h1 h2
    have hj : r - 1 < lcmUpTo K - 1 := by omega
    set j : Fin (lcmUpTo K - 1) := ⟨r - 1, hj⟩ with hjdef
    have hjr : (j : ℕ) + 1 = r := by simp only [hjdef]; omega
    have h := hneg ((Pi.single j 1 : Fin (lcmUpTo K - 1) → ℝ), (0 : ℝ))
      (by
        intro j'
        by_cases hjj : j' = j
        · subst hjj
          simp
        · simp [Pi.single_eq_of_ne hjj])
      le_rfl
    have hval : phi K S ((Pi.single j 1 : Fin (lcmUpTo K - 1) → ℝ), (0 : ℝ)) =
        (fun i : Fin (K - 1) => ((r % ((i : ℕ) + 2) : ℕ) : ℝ), if r ∈ S then (1 : ℝ) else 0) := by
      refine Prod.ext (funext fun i => ?_) ?_
      · simp only [phi]
        rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
        rw [Pi.single_eq_same, one_mul, hjr]
      · simp only [phi, sub_zero]
        rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
        rw [Pi.single_eq_same, mul_one, hjr]
    rw [hval, hdual] at h
    rw [hsaw]
    split_ifs at h ⊢ <;> linarith
  have hlogpos : α < -objective q K + lpValue K S * τ := by
    rw [hobj, neg_neg]
    have := hα
    rwa [hdual] at this
  rcases hτ0.eq_or_lt with hτz | hτpos
  · -- With `τ = 0` the weights are nonnegative on the period at negative cost.
    have hF : ∀ r, 0 ≤ saw q K r := by
      intro r
      rw [← saw_mod]
      rcases Nat.eq_zero_or_pos (r % lcmUpTo K) with h | h
      · rw [h, saw_zero]
      · have := hres _ h (Nat.mod_lt _ (lcmUpTo_pos K))
        rw [← hτz] at this
        simpa using this
    have hnn : 0 ≤ objective q K := ((isFakePrimeMeasure_pronic K).hasSum_saw q).nonneg
      fun j => mul_nonneg (by positivity) (hF _)
    rw [← hτz, mul_zero, add_zero] at hlogpos
    linarith
  · -- With `τ > 0` the rescaled weights are feasible below the value.
    set q' : ℕ → ℝ := fun k => q k / τ with hq'
    have hsaw' : ∀ r, saw q' K r = saw q K r / τ := by
      intro r
      rw [saw, saw, sum_div]
      exact sum_congr rfl fun k _ => by rw [hq']; ring
    have hF : IsFeasible K S q' := by
      refine ⟨fun r h1 h2 => ?_, fun r hr => ?_⟩
      · rw [hsaw']
        refine div_nonneg ?_ hτpos.le
        have := hres r h1 h2
        split_ifs at this <;> linarith
      · rw [hsaw', le_div_iff₀ hτpos, one_mul]
        have := hres r (hS r hr).1 (hS r hr).2
        rwa [if_pos hr] at this
    have hobj' : objective q' K = objective q K / τ := by
      rw [objective, objective, sum_div]
      exact sum_congr rfl fun k _ => by rw [hq']; ring
    have hle := lpValue_le hF
    rw [hobj', le_div_iff₀ hτpos] at hle
    nlinarith

/-- **Integer stencils approach the program.** Every feasible real weight is approached in cost by an integer shape producer on the same
alphabet and target. -/
theorem exists_shape_of_feasible {K : ℕ} {S : Finset ℕ} {q : ℕ → ℝ} (hK : 2 ≤ K)
    (hS : ∀ r ∈ S, 1 ≤ r ∧ r < lcmUpTo K) (hF : IsFeasible K S q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (c : ℕ →₀ ℤ) (m : ℕ), IsShapeProducer c m S ∧ AlphabetLE c K ∧
      stencilSlope c ≤ (m : ℝ) * (objective q K + δ) := by
  classical
  set W := objective (fun _ => 1) K with hW
  have hW0 : 0 ≤ W := (isFeasible_const hS).objective_nonneg
  have ho0 := hF.objective_nonneg
  set η := δ / (objective q K + 2 * W + 1) with hη
  have hdenom : 0 < objective q K + 2 * W + 1 := by linarith
  have hη0 : 0 < η := div_pos hδ hdenom
  have hKR : (2 : ℝ) ≤ K := by exact_mod_cast hK
  set ξ := η / ((K : ℝ) * K) with hξ
  have hξ0 : 0 < ξ := by positivity
  have hξη : ξ ≤ η := by
    rw [hξ]
    refine div_le_self hη0.le ?_
    nlinarith
  -- A rational point near the interior direction.
  set q₂ : ℕ → ℝ := fun k => (1 + η) * q k + η with hq₂
  have hrat : ∀ k, ∃ x : ℚ, q₂ k - ξ < x ∧ (x : ℝ) < q₂ k + ξ := fun k =>
    exists_rat_btwn (by linarith)
  choose x hx1 hx2 using hrat
  have hsaw2 : ∀ r, saw q₂ K r = (1 + η) * saw q K r + η * saw (fun _ => 1) K r := by
    intro r
    simp only [saw, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by rw [hq₂]; ring
  -- The rational sawtooth stays within `ξ K²` of the real one.
  have hclose : ∀ r, saw q₂ K r - η ≤ ∑ k ∈ Icc 2 K, (x k : ℝ) * ((r % k : ℕ) : ℝ) := by
    intro r
    have hterm : ∀ k ∈ Icc 2 K, q₂ k * ((r % k : ℕ) : ℝ) - ξ * K ≤ (x k : ℝ) * ((r % k : ℕ) : ℝ) := by
      intro k hk
      have hk' := mem_Icc.mp hk
      have hmod : ((r % k : ℕ) : ℝ) ≤ K := by
        have : r % k ≤ K := (Nat.mod_lt _ (by omega)).le.trans hk'.2
        exact_mod_cast this
      have hmod0 : (0 : ℝ) ≤ ((r % k : ℕ) : ℝ) := Nat.cast_nonneg _
      have h1 := hx1 k
      nlinarith
    have hsum := sum_le_sum hterm
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, Nat.card_Icc] at hsum
    have hcard : ((K + 1 - 2 : ℕ) : ℝ) ≤ K := by
      have : K + 1 - 2 ≤ K := by omega
      exact_mod_cast this
    have hbig : ((K + 1 - 2 : ℕ) : ℝ) * (ξ * K) ≤ η := by
      have hxiK : ξ * ((K : ℝ) * K) = η := by
        rw [hξ]
        field_simp
      calc ((K + 1 - 2 : ℕ) : ℝ) * (ξ * K) ≤ (K : ℝ) * (ξ * K) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = ξ * ((K : ℝ) * K) := by ring
        _ = η := hxiK
    have hsaw : saw q₂ K r = ∑ k ∈ Icc 2 K, q₂ k * ((r % k : ℕ) : ℝ) := rfl
    rw [hsaw]
    linarith
  have hnn : ∀ r, 0 ≤ ∑ k ∈ Icc 2 K, (x k : ℝ) * ((r % k : ℕ) : ℝ) := by
    intro r
    have hper : ∑ k ∈ Icc 2 K, (x k : ℝ) * ((r % k : ℕ) : ℝ) =
        ∑ k ∈ Icc 2 K, (x k : ℝ) * (((r % lcmUpTo K) % k : ℕ) : ℝ) :=
      sum_congr rfl fun k hk => by rw [Nat.mod_mod_of_dvd _ (dvd_lcmUpTo hk)]
    rw [hper]
    rcases Nat.eq_zero_or_pos (r % lcmUpTo K) with h | h
    · simp [h]
    · have hL := Nat.mod_lt r (lcmUpTo_pos K)
      refine le_trans ?_ (hclose _)
      rw [hsaw2]
      have h1 := hF.nonneg _ h hL
      have h2 := one_le_saw_one h hL
      nlinarith
  have hwin : ∀ r ∈ S, 1 ≤ ∑ k ∈ Icc 2 K, (x k : ℝ) * ((r % k : ℕ) : ℝ) := by
    intro r hr
    refine le_trans ?_ (hclose r)
    rw [hsaw2]
    have h1 := hF.target r hr
    have h2 := one_le_saw_one (hS r hr).1 (hS r hr).2
    nlinarith
  obtain ⟨c, m, hm, hc0, hbal, hstep, hslope, hsupp, -⟩ := exists_stencil_of_weights (J := Icc 2 K) x
    (fun k hk => (mem_Icc.mp hk).1)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hshape : IsShapeProducer c m S := by
    refine ⟨hc0, hbal, fun r => ?_, hm, fun r hr => ?_⟩
    · have hR : (0 : ℝ) ≤ (stepWeight c r : ℝ) := by
        rw [hstep r]
        exact mul_nonneg hmR.le (hnn r)
      exact_mod_cast hR
    · have hR : ((m : ℤ) : ℝ) ≤ (stepWeight c r : ℝ) := by
        rw [hstep r]
        push_cast
        calc (m : ℝ) = (m : ℝ) * 1 := (mul_one _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left (hwin r hr) hmR.le
      exact_mod_cast hR
  have hal : AlphabetLE c K := by
    intro k hk
    rcases mem_insert.mp (hsupp hk) with h | h
    · omega
    · exact (mem_Icc.mp h).2
  refine ⟨c, m, hshape, hal, ?_⟩
  rw [hslope]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m)
  -- The cost of the rational point.
  have hcost : ∑ k ∈ Icc 2 K, (x k : ℝ) * Real.log k ≤ (1 + η) * objective q K + η * W + ξ * W := by
    have hterm : ∀ k ∈ Icc 2 K, (x k : ℝ) * Real.log k ≤
        (1 + η) * (q k * Real.log k) + η * (1 * Real.log k) + ξ * (1 * Real.log k) := by
      intro k _
      have hlog : 0 ≤ Real.log k := Real.log_natCast_nonneg k
      have h2 := hx2 k
      have h3 : (x k : ℝ) ≤ (1 + η) * q k + η + ξ := by
        have : q₂ k = (1 + η) * q k + η := rfl
        linarith
      calc (x k : ℝ) * Real.log k ≤ ((1 + η) * q k + η + ξ) * Real.log k :=
            mul_le_mul_of_nonneg_right h3 hlog
        _ = _ := by ring
    refine (sum_le_sum hterm).trans (le_of_eq ?_)
    rw [hW]
    simp only [objective, sum_add_distrib, mul_sum]
  have hfinal : η * (objective q K + 2 * W + 1) = δ := by
    rw [hη]
    field_simp
  nlinarith

/-- **Integer producers approach the program at a window.** -/
theorem exists_producer_of_feasible {K B : ℕ} {q : ℕ → ℝ} (hK : 2 ≤ K) (hB : 2 ≤ B)
    (hBL : B ≤ lcmUpTo K) (hF : IsFeasible K (Ico 1 B) q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (c : ℕ →₀ ℤ) (m : ℕ), IsProducer c m B ∧ AlphabetLE c K ∧
      stencilSlope c ≤ (m : ℝ) * (objective q K + δ) := by
  obtain ⟨c, m, h, hal, hs⟩ := exists_shape_of_feasible hK (mem_window hBL) hF hδ
  exact ⟨c, m, ⟨h.zero, h.balanced, h.nonneg, h.one_le_m, hB, h.target⟩, hal, hs⟩

/-- **The extremal fake prime measure of a target.** For an alphabet `[2, K]` and a finite target inside one period there is a fake prime
measure, supported on one period, of largest mass on the target, and that mass is approached by the slopes of integer shape producers. -/
theorem exists_extremal_of_target {K : ℕ} {S : Finset ℕ} (hK : 2 ≤ K) (hS : ∀ r ∈ S, 1 ≤ r ∧ r < lcmUpTo K) :
    ∃ u : ℕ → ℝ, IsFakePrimeMeasure K u ∧ (∀ j, lcmUpTo K ≤ j + 1 → u j = 0) ∧
      (∀ v : ℕ → ℝ, IsFakePrimeMeasure K v → targetMass v S ≤ targetMass u S) ∧
      (∀ δ > 0, ∃ (c : ℕ →₀ ℤ) (m : ℕ), IsShapeProducer c m S ∧ AlphabetLE c K ∧
        stencilSlope c ≤ (m : ℝ) * (targetMass u S + δ)) ∧ targetMass u S = lpValue K S := by
  classical
  obtain ⟨⟨w, t⟩, ⟨hw, ht⟩, hphi⟩ := exists_dual_point (K := K) hS
  change 0 ≤ w at hw
  change 0 ≤ t at ht
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, u = fun j => if h : j < lcmUpTo K - 1 then w ⟨j, h⟩ else 0 := ⟨_, rfl⟩
  have huval : ∀ j : Fin (lcmUpTo K - 1), u j = w j := fun j => by
    simp only [hu, dif_pos j.2]
  have hu0 : ∀ j, 0 ≤ u j := by
    intro j
    simp only [hu]
    split_ifs with h
    · exact hw ⟨j, h⟩
    · exact le_rfl
  have hoff : ∀ j, lcmUpTo K ≤ j + 1 → u j = 0 := by
    intro j hj
    have hL := lcmUpTo_pos K
    simp only [hu]
    rw [dif_neg (by omega)]
  have hsumFin : ∀ g : ℕ → ℝ, ∑ j : Fin (lcmUpTo K - 1), w j * g j = ∑ j ∈ range (lcmUpTo K - 1), u j * g j := by
    intro g
    rw [← Fin.sum_univ_eq_sum_range (fun j => u j * g j) (lcmUpTo K - 1)]
    exact sum_congr rfl fun j _ => by rw [huval]
  have hfake : IsFakePrimeMeasure K u := by
    refine ⟨hu0, fun k hk => ?_⟩
    obtain ⟨hk1, hkK⟩ := mem_Icc.mp hk
    rcases eq_or_lt_of_le hk1 with h1 | h2
    · subst h1
      simp [Nat.mod_one]
    · have hi : k - 2 < K - 1 := by omega
      have hmom := congrFun (congrArg Prod.fst hphi) ⟨k - 2, hi⟩
      simp only [phi] at hmom
      have hkk : k - 2 + 2 = k := by omega
      simp only [hkk] at hmom
      have hval := hsumFin fun j => (((j + 1) % k : ℕ) : ℝ)
      rw [hmom] at hval
      rw [hval]
      refine hasSum_sum_of_ne_finset_zero fun j hj => ?_
      have hjn : ¬ j < lcmUpTo K - 1 := fun h => hj (mem_range.mpr h)
      simp only [hu, dif_neg hjn, zero_mul]
  -- The mass on the target dominates the value.
  have hinj : Set.InjOn (fun r : ℕ => r - 1) (S : Set ℕ) := by
    intro a ha b hb hab
    have h1 := (hS a ha).1
    have h2 := (hS b hb).1
    simp only at hab
    omega
  have hmass : (∑ j : Fin (lcmUpTo K - 1), (if (j : ℕ) + 1 ∈ S then (1 : ℝ) else 0) * w j) = targetMass u S := by
    have h1 : ∑ j : Fin (lcmUpTo K - 1), (if (j : ℕ) + 1 ∈ S then (1 : ℝ) else 0) * w j =
        ∑ j ∈ range (lcmUpTo K - 1), u j * (if j + 1 ∈ S then (1 : ℝ) else 0) := by
      rw [← hsumFin]
      exact sum_congr rfl fun j _ => by ring
    have hsub : S.image (fun r => r - 1) ⊆ range (lcmUpTo K - 1) := by
      intro j hj
      obtain ⟨r, hr, rfl⟩ := mem_image.mp hj
      have := hS r hr
      exact mem_range.mpr (by omega)
    rw [h1, ← sum_subset hsub (fun j _ hj => by
      have hj' : j + 1 ∉ S := fun h => hj (mem_image.mpr ⟨j + 1, h, by simp⟩)
      simp [hj'])]
    rw [targetMass, ← sum_image (f := u) hinj]
    refine sum_congr rfl fun j hj => ?_
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hj
    have e : r - 1 + 1 = r := by have := (hS r hr).1; omega
    simp [e, hr]
  have hsnd := congrArg Prod.snd hphi
  simp only [phi] at hsnd
  rw [hmass] at hsnd
  have htt : (0 : ℝ) ≤ t := ht
  have hvalue : lpValue K S ≤ targetMass u S := by linarith
  have hne : {x | ∃ q, IsFeasible K S q ∧ objective q K = x}.Nonempty :=
    ⟨_, _, isFeasible_const hS, rfl⟩
  refine ⟨u, hfake, hoff, fun v hv => ?_, fun δ hδ => ?_, ?_⟩
  · -- Any consistent measure has mass at most every cost, hence at most the value.
    have hbound : ∀ x ∈ {x | ∃ q, IsFeasible K S q ∧ objective q K = x}, targetMass v S ≤ x := by
      rintro x ⟨q, hq, rfl⟩
      exact hq.mass_le (fun r hr => (hS r hr).1) hv
    exact (le_csInf hne hbound).trans hvalue
  · obtain ⟨x, ⟨q, hq, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt hne (by linarith : lpValue K S < lpValue K S + δ / 2)
    obtain ⟨c, m, hP, hal, hs⟩ := exists_shape_of_feasible hK hS hq (half_pos hδ)
    refine ⟨c, m, hP, hal, hs.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg m))⟩
    linarith
  · -- The mass is the value of the program.
    refine le_antisymm (le_csInf hne ?_) hvalue
    rintro x ⟨q, hq, rfl⟩
    exact hq.mass_le (fun r hr => (hS r hr).1) hfake

/-- **The extremal fake prime measure.** For an alphabet `[2, K]` and a window with `B` at most the period,
there is a fake prime measure, supported on one period, whose window mass is approached by the slopes of integer
producers. Together with `IsFakePrimeMeasure.le_normSlope` this is the exact value of the best normalized slope at
window `B`, and no fake prime measure has larger window mass. -/
theorem exists_extremal_fake_measure {K B : ℕ} (hK : 2 ≤ K) (hB : 2 ≤ B) (hBL : B ≤ lcmUpTo K) :
    ∃ u : ℕ → ℝ, IsFakePrimeMeasure K u ∧ (∀ j, lcmUpTo K ≤ j + 1 → u j = 0) ∧
      (∀ v : ℕ → ℝ, IsFakePrimeMeasure K v →
        ∑ j ∈ range (B - 1), v j ≤ ∑ j ∈ range (B - 1), u j) ∧
      ∀ δ > 0, ∃ (c : ℕ →₀ ℤ) (m : ℕ), IsProducer c m B ∧ AlphabetLE c K ∧
        stencilSlope c ≤ (m : ℝ) * (∑ j ∈ range (B - 1), u j + δ) := by
  obtain ⟨u, hu, hoff, hmax, hprod, -⟩ := exists_extremal_of_target hK (mem_window hBL)
  refine ⟨u, hu, hoff, fun v hv => ?_, fun δ hδ => ?_⟩
  · have := hmax v hv
    rwa [targetMass_Ico, targetMass_Ico] at this
  · obtain ⟨c, m, h, hal, hs⟩ := hprod δ hδ
    rw [targetMass_Ico] at hs
    exact ⟨c, m, ⟨h.zero, h.balanced, h.nonneg, h.one_le_m, hB, h.target⟩, hal, hs⟩

/-- **The excess is an integral of slack.** Against any fake prime measure, the slope minus `m` times the window
mass is the sum of `u(r)` times the slack of the multiplicity. An extremal measure lives where the slack is small. -/
theorem IsFakePrimeMeasure.hasSum_slack {K : ℕ} {u : ℕ → ℝ} (hu : IsFakePrimeMeasure K u)
    {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) (hK : AlphabetLE c K) :
    HasSum (fun j => u j * ((stepWeight c (j + 1) : ℝ) - if j ∈ range (B - 1) then (m : ℝ) else 0))
      (stencilSlope c - (m : ℝ) * ∑ j ∈ range (B - 1), u j) := by
  have h1 := hu.hasSum_slope hP hK
  have h2 : HasSum (fun j => u j * (if j ∈ range (B - 1) then (m : ℝ) else 0))
      ((m : ℝ) * ∑ j ∈ range (B - 1), u j) := by
    have h3 : HasSum (fun j : ℕ => u j * (if j ∈ range (B - 1) then (m : ℝ) else 0))
        (∑ j ∈ range (B - 1), u j * (if j ∈ range (B - 1) then (m : ℝ) else 0)) :=
      hasSum_sum_of_ne_finset_zero fun j hj => by simp [hj]
    have h4 : ∑ j ∈ range (B - 1), u j * (if j ∈ range (B - 1) then (m : ℝ) else 0) =
        (m : ℝ) * ∑ j ∈ range (B - 1), u j := by
      rw [mul_sum]
      exact sum_congr rfl fun j hj => by rw [if_pos hj]; ring
    rwa [h4] at h3
  have h5 := h1.sub h2
  have hfun : (fun j => u j * ((stepWeight c (j + 1) : ℝ) - if j ∈ range (B - 1) then (m : ℝ) else 0)) =
      fun j => u j * (stepWeight c (j + 1) : ℝ) - u j * (if j ∈ range (B - 1) then (m : ℝ) else 0) := by
    funext j
    ring
  rw [hfun]
  exact h5
/-- A producer's window lies inside one period of its alphabet. -/
theorem IsProducer.le_lcmUpTo {c : ℕ →₀ ℤ} {m B K : ℕ} (hP : IsProducer c m B) (hK : AlphabetLE c K) :
    B ≤ lcmUpTo K := by
  by_contra hlt
  push Not at hlt
  have hL := lcmUpTo_pos K
  have hw := hP.window (lcmUpTo K) (mem_Ico.mpr ⟨hL, hlt⟩)
  have h0 : stepWeight c (lcmUpTo K) = 0 := by
    have hR : (stepWeight c (lcmUpTo K) : ℝ) = 0 := by
      rw [stepWeight_eq_sum_mod hP.zero hP.balanced]
      refine sum_eq_zero fun k hk => ?_
      have hk0 : k ≠ 0 := fun h => by
        subst h
        exact Finsupp.mem_support_iff.mp hk hP.zero
      by_cases h1 : k = 1
      · subst h1
        simp [Nat.mod_one]
      · have hd := dvd_lcmUpTo (K := K) (mem_Icc.mpr ⟨by omega, hK k hk⟩)
        rw [Nat.mod_eq_zero_of_dvd hd]
        simp
    exact_mod_cast hR
  rw [h0] at hw
  have := hP.one_le_m
  omega

/-- **No fake prime measure of level `K` is extremal near the truth.** A measure whose window mass is approached by integer producers
exceeds the pronic mass `1 − 1/B` by a factor at least `1 + c₁/(√K (1 + log K))`. -/
theorem exists_extremal_gap :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (K B : ℕ) (u : ℕ → ℝ), 1 ≤ K → 2 ≤ B →
      (∀ δ > 0, ∃ (c : ℕ →₀ ℤ) (m : ℕ), IsProducer c m B ∧ AlphabetLE c K ∧
        stencilSlope c ≤ (m : ℝ) * (∑ j ∈ range (B - 1), u j + δ)) →
      (1 - 1 / (B : ℝ)) * (1 + c₁ / (√(K : ℝ) * (1 + Real.log K))) ≤ ∑ j ∈ range (B - 1), u j := by
  obtain ⟨c₁, hc₁, hfloor⟩ := exists_half_floor
  refine ⟨c₁, hc₁, fun K B u hK hB hprod => le_of_forall_pos_le_add fun δ hδ => ?_⟩
  obtain ⟨c, m, hP, hal, hs⟩ := hprod δ hδ
  have hm := hP.m_pos
  have hd := hP.one_sub_pos
  have hf := hfloor K c m B hK hP hal
  have hrate : rate c m B = stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ))) - 1 := rfl
  have h1 : 1 + c₁ / (√(K : ℝ) * (1 + Real.log K)) ≤ stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ))) := by
    rw [hrate] at hf
    linarith
  rw [le_div_iff₀ (mul_pos hm hd)] at h1
  have h2 := h1.trans hs
  have h3 : (m : ℝ) * ((1 - 1 / (B : ℝ)) * (1 + c₁ / (√(K : ℝ) * (1 + Real.log K)))) ≤
      (m : ℝ) * (∑ j ∈ range (B - 1), u j + δ) := by
    calc _ = (1 + c₁ / (√(K : ℝ) * (1 + Real.log K))) * ((m : ℝ) * (1 - 1 / (B : ℝ))) := by ring
      _ ≤ _ := h2
  exact le_of_mul_le_mul_left h3 hm

/-- **How close the extremal measure is.** For `0 < α < 3/5` and all large `K` there is a window at which the extremal fake prime measure has
window mass between `(1 − 1/B)(1 + c₁/(√K (1 + log K)))` and `(1 − 1/B)(1 + exp(−(log K)^α))`. -/
theorem exists_extremal_bracket {α : ℝ} (hα0 : 0 < α) (hα : α < 3 / 5) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ K : ℕ in atTop, ∃ (B : ℕ) (u : ℕ → ℝ), 2 ≤ B ∧ IsFakePrimeMeasure K u ∧
      (∀ v : ℕ → ℝ, IsFakePrimeMeasure K v → ∑ j ∈ range (B - 1), v j ≤ ∑ j ∈ range (B - 1), u j) ∧
      (1 - 1 / (B : ℝ)) * (1 + c₁ / (√(K : ℝ) * (1 + Real.log K))) ≤ ∑ j ∈ range (B - 1), u j ∧
      ∑ j ∈ range (B - 1), u j ≤ (1 - 1 / (B : ℝ)) * (1 + Real.exp (-(Real.log (K : ℝ) ^ α))) := by
  obtain ⟨c₁, hc₁, hgap⟩ := exists_extremal_gap
  refine ⟨c₁, hc₁, ?_⟩
  filter_upwards [hasRate_vk hα0 hα, eventually_ge_atTop 2] with K hK hK2
  obtain ⟨c, m, B, hP, hal, hr⟩ := hK
  have hB := hP.two_le_B
  obtain ⟨u, hu, _, hmax, hprod⟩ := exists_extremal_fake_measure hK2 hB (hP.le_lcmUpTo hal)
  refine ⟨B, u, hB, hu, hmax, hgap K B u (by omega) hB hprod, ?_⟩
  have hd := hP.one_sub_pos
  have h1 := hu.le_normSlope hP hal
  rw [div_le_iff₀ hd] at h1
  have h2 : normSlope c m B = 1 + rate c m B := by
    rw [rate]
    ring
  calc ∑ j ∈ range (B - 1), u j ≤ normSlope c m B * (1 - 1 / (B : ℝ)) := h1
    _ = (1 + rate c m B) * (1 - 1 / (B : ℝ)) := by rw [h2]
    _ ≤ (1 + Real.exp (-(Real.log (K : ℝ) ^ α))) * (1 - 1 / (B : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) hd.le
    _ = _ := by ring

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
