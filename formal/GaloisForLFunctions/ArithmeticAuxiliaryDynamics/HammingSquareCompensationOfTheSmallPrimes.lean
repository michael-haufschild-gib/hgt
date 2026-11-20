import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheTautStringSmoothMertensStencil
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheCompensatedProducer
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Bertrand

/-!
# Hamming-square compensation of the small primes

Given an integer stencil `b` supported in `[1, N]` whose partial sums track `M(x)` within `η₀ x`
for all `x ≥ 1`, whose active letters `k ≥ 2` satisfy `¬ 4 ∣ k` with `b 2 = -1`, and whose prime
powers dividing active letters are at most `P_max`, we assemble an admissible balanced integer
producer on `[1, K]` with window `B₀ ≍ K / W` using two elementary devices:

1. **Bipartite Hamming-square cofactor clusters.** For each odd prime power `Q = q^e ≤ P_max`, we
   form the full Cartesian square of moduli `L_Q(p₁, p₂) = 2^{b_Q} p₁ p₂ Q ≤ K` over primes
   `p₁, p₂ ∈ P_W \ {q}`, where `P_W = {p prime : W < p ≤ 2^S W}` has `|P_W| ≥ S = 16 M₀ + 4` by
   iterated Bertrand's postulate. Whenever fewer than `|P_{W,Q}|² / (16 M₀)` pairs have residue
   `≥ B₀`, row/column majority forces more than `(1 - 1 / (8 M₀))|P_W| - 1` primes `p ∈ P_W` to
   share a single common residue `h_Q = r mod (2^{b_Q} p Q) < B₀`, giving `2 ∣ r - h_Q`,
   `Q ∣ r - h_Q`, and `p ∣ r - h_Q`.
2. **Subset-product CRT ramp.** Averaging `r mod (∏_{p ∈ A} p)` over all `m_*`-element subsets
   `A ⊆ P_W` (`m_* = ⌊log_{2^S W} K⌋ < M₀`) forces any two aligned prime powers `Q₁, Q₂` to
   agree (`h_{Q₁} = h_{Q₂}`) and retains at least half of all `m_*`-subsets inside the aligned
   prime pool, supplying the linear drift restoration `2 Y_n h` at `h < B₀`.
-/

open Finset Filter Topology
open scoped Classical
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-! ### Part 1: Near sawtooth, drift reading, and pronic slope for a Mertens-tracking stencil -/

/-- Near sawtooth of an integer stencil `b` supported on `[1, N]`. -/
def tautNear (b : ℕ → ℤ) (N r : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 N, (-(b k : ℝ) / k) * ((r % k : ℕ) : ℝ)

/-- Harmonic drift `∑_{1 ≤ k ≤ N} b(k) / k` of an integer stencil `b`. -/
def tautTheta (b : ℕ → ℤ) (N : ℕ) : ℝ :=
  ∑ k ∈ Ioc 0 N, (b k : ℝ) / k

/-- `ℓ¹` mass `∑_{2 ≤ k ≤ N} |b(k)|` of the non-unit letters of `b`. -/
def tautMass (b : ℕ → ℤ) (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 N, |(b k : ℝ)|

/-- Logarithmic slope `∑_{2 ≤ k ≤ N} (-b(k) / k) log k` of the near stencil. -/
def tautSlope (b : ℕ → ℤ) (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 2 N, (-(b k : ℝ) / k) * Real.log k

theorem tautMass_nonneg (b : ℕ → ℤ) (N : ℕ) : 0 ≤ tautMass b N :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem tautNear_zero (b : ℕ → ℤ) (N : ℕ) : tautNear b N 0 = 0 := by
  simp [tautNear]

theorem abs_tautNear_le (b : ℕ → ℤ) (N r : ℕ) : |tautNear b N r| ≤ tautMass b N := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  have hk2 := (mem_Icc.mp hk).1
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hmod : ((r % k : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.mod_lt r (by omega)).le
  rw [abs_mul, abs_div, abs_neg, abs_of_pos hkR, Nat.abs_cast]
  have h0 := abs_nonneg (b k : ℝ)
  calc |(b k : ℝ)| / k * ((r % k : ℕ) : ℝ) ≤ |(b k : ℝ)| / k * k := by gcongr
    _ = |(b k : ℝ)| := by field_simp

/-- Dirichlet hyperbola identity on `[1, s]`:
`∑_{1 ≤ k ≤ s} c(k) ⌊s / k⌋ = ∑_{1 ≤ j ≤ s} ∑_{1 ≤ k ≤ ⌊s / j⌋} c(k)`. -/
private lemma sum_Icc_one_mul_floor (c : ℕ → ℝ) (s : ℕ) :
    ∑ k ∈ Icc 1 s, c k * ((s / k : ℕ) : ℝ) =
      ∑ j ∈ Icc 1 s, ∑ k ∈ Icc 1 (s / j), c k := by
  have hcount : ∀ k ∈ Icc 1 s, ((s / k : ℕ) : ℝ) =
      ∑ j ∈ Icc 1 s, if k ≤ s / j then (1 : ℝ) else 0 := by
    intro k hk
    obtain ⟨hk1, -⟩ := mem_Icc.mp hk
    have hk0 : 0 < k := by omega
    have hfil : (Icc 1 s).filter (fun j => k ≤ s / j) = Ioc 0 (s / k) := by
      ext j
      simp only [mem_filter, mem_Icc, mem_Ioc]
      constructor
      · rintro ⟨⟨hj1, -⟩, hj⟩
        refine ⟨by omega, (Nat.le_div_iff_mul_le hk0).mpr ?_⟩
        have := (Nat.le_div_iff_mul_le (by omega : 0 < j)).mp hj
        rwa [mul_comm] at this
      · rintro ⟨hj0, hj⟩
        refine ⟨⟨hj0, hj.trans (Nat.div_le_self s k)⟩, (Nat.le_div_iff_mul_le hj0).mpr ?_⟩
        have := (Nat.le_div_iff_mul_le hk0).mp hj
        rwa [mul_comm] at this
    rw [← sum_filter, hfil]
    simp
  have hsw : ∑ k ∈ Icc 1 s, c k * ((s / k : ℕ) : ℝ) =
      ∑ j ∈ Icc 1 s, ∑ k ∈ Icc 1 s, c k * (if k ≤ s / j then (1 : ℝ) else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun k hk => ?_
    rw [hcount k hk, mul_sum]
  rw [hsw]
  refine sum_congr rfl fun j _ => ?_
  have hle : s / j ≤ s := Nat.div_le_self _ _
  have hfil : (Icc 1 s).filter (fun k => k ≤ s / j) = Icc 1 (s / j) := by
    ext k
    simp only [mem_filter, mem_Icc]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hle⟩, h.2⟩⟩
  rw [← hfil, sum_filter]
  refine sum_congr rfl fun _ _ => ?_
  split_ifs <;> simp

private lemma tautNear_eq_floor {b : ℕ → ℤ} {N : ℕ} (hN : 1 ≤ N) (hb1 : b 1 = 1)
    (hb_supp : ∀ k : ℕ, N < k → b k = 0) (s : ℕ) :
    tautNear b N s = ∑ k ∈ Icc 1 s, (b k : ℝ) * ((s / k : ℕ) : ℝ) - tautTheta b N * s := by
  have hset : Ioc 0 N = insert 1 (Icc 2 N) := by
    ext k; simp only [mem_Ioc, mem_insert, mem_Icc]; omega
  have h1 : (1 : ℕ) ∉ Icc 2 N := by simp
  have hnear : tautNear b N s =
      ∑ k ∈ Ioc 0 N, (b k : ℝ) * ((s / k : ℕ) : ℝ) - tautTheta b N * s := by
    rw [tautTheta, hset, sum_insert h1, sum_insert h1, tautNear]
    have hrest : ∑ k ∈ Icc 2 N, (-(b k : ℝ) / k) * ((s % k : ℕ) : ℝ) =
        ∑ k ∈ Icc 2 N, (b k : ℝ) * ((s / k : ℕ) : ℝ) -
          (∑ k ∈ Icc 2 N, (b k : ℝ) / k) * s := by
      rw [sum_mul, ← sum_sub_distrib]
      refine sum_congr rfl fun k hk => ?_
      have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Icc.mp hk).1; omega)
      have hd : (s : ℝ) = (k : ℝ) * ((s / k : ℕ) : ℝ) + ((s % k : ℕ) : ℝ) := by
        exact_mod_cast (Nat.div_add_mod s k).symm
      have hm : ((s % k : ℕ) : ℝ) = (s : ℝ) - (k : ℝ) * ((s / k : ℕ) : ℝ) := by linarith
      rw [hm]; field_simp; ring
    rw [hrest, hb1]
    simp only [Int.cast_one, Nat.div_one, Nat.cast_one, div_one]
    ring
  rw [hnear]
  congr 1
  have hIoc : Ioc 0 N = Icc 1 N := by ext k; simp [mem_Ioc, mem_Icc]; omega
  rw [hIoc]
  rcases le_total N s with hNs | hsN
  · have hsplit : Icc 1 s = Icc 1 N ∪ Ioc N s := by
      ext k; simp [mem_Icc, mem_union, mem_Ioc]; omega
    have hdisj : Disjoint (Icc 1 N) (Ioc N s) := by
      rw [Finset.disjoint_left]; intro k hk1 hk2
      rw [mem_Icc] at hk1; rw [mem_Ioc] at hk2; omega
    rw [hsplit, sum_union hdisj]
    have hz : ∑ k ∈ Ioc N s, (b k : ℝ) * ((s / k : ℕ) : ℝ) = 0 :=
      sum_eq_zero fun k hk => by rw [hb_supp k (mem_Ioc.mp hk).1]; simp
    rw [hz, add_zero]
  · have hsplit : Icc 1 N = Icc 1 s ∪ Ioc s N := by
      ext k; simp [mem_Icc, mem_union, mem_Ioc]; omega
    have hdisj : Disjoint (Icc 1 s) (Ioc s N) := by
      rw [Finset.disjoint_left]; intro k hk1 hk2
      rw [mem_Icc] at hk1; rw [mem_Ioc] at hk2; omega
    rw [hsplit, sum_union hdisj]
    have hz : ∑ k ∈ Ioc s N, (b k : ℝ) * ((s / k : ℕ) : ℝ) = 0 :=
      sum_eq_zero fun k hk => by rw [Nat.div_eq_of_lt (mem_Ioc.mp hk).1]; simp
    rw [hz, add_zero]

private lemma abs_sum_floor_sub_one_le {b : ℕ → ℤ} {η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    (hB : ∀ x : ℕ, 1 ≤ x → |(∑ k ∈ Icc 1 x, (b k : ℝ)) - mertens x| ≤ η₀ * (x : ℝ))
    {s : ℕ} (hs : 1 ≤ s) :
    |(∑ k ∈ Icc 1 s, (b k : ℝ) * ((s / k : ℕ) : ℝ)) - 1| ≤
      η₀ * (s : ℝ) * (1 + Real.log (s : ℝ)) := by
  have hmoeb := RHTower.moebius_floor_summatory s hs
  have hlhs : (∑ k ∈ Icc 1 s, (b k : ℝ) * ((s / k : ℕ) : ℝ)) - 1 =
      ∑ j ∈ Icc 1 s, ∑ k ∈ Icc 1 (s / j),
        ((b k : ℝ) - (ArithmeticFunction.moebius k : ℝ)) := by
    rw [← hmoeb, ← sum_sub_distrib]
    have hsub_eq : ∑ k ∈ Icc 1 s,
        ((b k : ℝ) * ((s / k : ℕ) : ℝ) - (ArithmeticFunction.moebius k : ℝ) * ((s / k : ℕ) : ℝ)) =
        ∑ k ∈ Icc 1 s, ((b k : ℝ) - (ArithmeticFunction.moebius k : ℝ)) * ((s / k : ℕ) : ℝ) :=
      sum_congr rfl fun _ _ => by ring
    rw [hsub_eq, sum_Icc_one_mul_floor]
  rw [hlhs]
  have hterm : ∀ j ∈ Icc 1 s,
      |∑ k ∈ Icc 1 (s / j), ((b k : ℝ) - (ArithmeticFunction.moebius k : ℝ))| ≤
        η₀ * (s : ℝ) * ((j : ℝ))⁻¹ := by
    intro j hj
    obtain ⟨hj1, hjs⟩ := mem_Icc.mp hj
    have hdiv1 : 1 ≤ s / j := (Nat.one_le_div_iff (by omega)).mpr hjs
    have hmert : ∑ k ∈ Icc 1 (s / j), (ArithmeticFunction.moebius k : ℝ) = mertens (s / j) := by
      rw [mertens]
      have hset : Icc 1 (s / j) = Ioc 0 (s / j) := by ext k; simp [mem_Icc, mem_Ioc]; omega
      rw [hset]
    rw [sum_sub_distrib, hmert]
    have hbd := hB (s / j) hdiv1
    have hdiv_le : ((s / j : ℕ) : ℝ) ≤ (s : ℝ) / (j : ℝ) := Nat.cast_div_le
    calc |(∑ k ∈ Icc 1 (s / j), (b k : ℝ)) - mertens (s / j)|
        ≤ η₀ * ((s / j : ℕ) : ℝ) := hbd
      _ ≤ η₀ * ((s : ℝ) / (j : ℝ)) := mul_le_mul_of_nonneg_left hdiv_le hη₀
      _ = η₀ * (s : ℝ) * ((j : ℝ))⁻¹ := by ring
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hH := harmonic_le_one_add_log s
  rw [harmonic_eq_sum_Icc] at hH
  push_cast at hH
  exact hH

/-- Reading the harmonic drift at `X ≥ 1` bounds `|tautNear b N s - 1|` uniformly on `[1, X]`. -/
theorem abs_tautNear_sub_one_le {b : ℕ → ℤ} {N X s : ℕ} {η₀ : ℝ}
    (hN : 1 ≤ N) (hb1 : b 1 = 1) (hb_supp : ∀ k : ℕ, N < k → b k = 0)
    (hη₀ : 0 ≤ η₀)
    (hB : ∀ x : ℕ, 1 ≤ x → |(∑ k ∈ Icc 1 x, (b k : ℝ)) - mertens x| ≤ η₀ * (x : ℝ))
    (hs1 : 1 ≤ s) (hsX : s ≤ X) :
    |tautNear b N s - 1| ≤
      (s : ℝ) * (2 * η₀ * (1 + Real.log (X : ℝ)) + (1 + tautMass b N) / (X : ℝ)) := by
  have hX1 : 1 ≤ X := hs1.trans hsX
  have hXR_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX1
  have hsR_pos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
  have hlog_le : Real.log (s : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hsR_pos (by exact_mod_cast hsX)
  have htheta_bd : |tautTheta b N| ≤
      η₀ * (1 + Real.log (X : ℝ)) + (1 + tautMass b N) / (X : ℝ) := by
    have hX_eq := tautNear_eq_floor hN hb1 hb_supp X
    have hX_fl := abs_sum_floor_sub_one_le hη₀ hB hX1
    have hX_near := abs_tautNear_le b N X
    have htheta_X : tautTheta b N * (X : ℝ) =
        ((∑ k ∈ Icc 1 X, (b k : ℝ) * ((X / k : ℕ) : ℝ)) - 1) + 1 - tautNear b N X := by
      linarith
    have habs_X : |tautTheta b N| * (X : ℝ) ≤
        η₀ * (X : ℝ) * (1 + Real.log (X : ℝ)) + 1 + tautMass b N := by
      have e : |tautTheta b N| * (X : ℝ) = |tautTheta b N * (X : ℝ)| := by
        rw [abs_mul, abs_of_pos hXR_pos]
      rw [e, htheta_X]
      have h1 := abs_sub (((∑ k ∈ Icc 1 X, (b k : ℝ) * ((X / k : ℕ) : ℝ)) - 1) + 1) (tautNear b N X)
      have h2 := abs_add_le ((∑ k ∈ Icc 1 X, (b k : ℝ) * ((X / k : ℕ) : ℝ)) - 1) 1
      rw [abs_one] at h2
      linarith
    rw [← le_div_iff₀ hXR_pos] at habs_X
    refine habs_X.trans_eq ?_
    field_simp [hXR_pos.ne']
    ring
  have hs_eq := tautNear_eq_floor hN hb1 hb_supp s
  have hs_fl := abs_sum_floor_sub_one_le hη₀ hB hs1
  have hsub : tautNear b N s - 1 =
      ((∑ k ∈ Icc 1 s, (b k : ℝ) * ((s / k : ℕ) : ℝ)) - 1) - tautTheta b N * (s : ℝ) := by
    linarith
  rw [hsub]
  refine (abs_sub _ _).trans ?_
  have hfl_X : η₀ * (s : ℝ) * (1 + Real.log (s : ℝ)) ≤ η₀ * (s : ℝ) * (1 + Real.log (X : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hth_s : |tautTheta b N * (s : ℝ)| ≤
      (s : ℝ) * (η₀ * (1 + Real.log (X : ℝ)) + (1 + tautMass b N) / (X : ℝ)) := by
    rw [abs_mul, abs_of_pos hsR_pos, mul_comm]
    exact mul_le_mul_of_nonneg_left htheta_bd hsR_pos.le
  linarith [hs_fl.trans hfl_X, hth_s]

private def pronicStep' (j : ℕ) : ℝ := 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))

private lemma pronicStep'_nonneg (j : ℕ) : 0 ≤ pronicStep' j := by
  rw [pronicStep']; positivity

private lemma sum_range_pronicStep' (n : ℕ) :
    ∑ j ∈ range n, pronicStep' j = 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pronicStep']
    push_cast; field_simp; ring

private lemma sum_Ico_pronicStep' {a b : ℕ} (h : a ≤ b) :
    ∑ j ∈ Ico a b, pronicStep' j = 1 / ((a : ℝ) + 1) - 1 / ((b : ℝ) + 1) := by
  rw [sum_Ico_eq_sub _ h, sum_range_pronicStep', sum_range_pronicStep']
  ring

private lemma sum_ite_lt_le'' {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (n G : ℕ) :
    ∑ j ∈ range n, (if j + 1 < G then a j else 0) ≤ ∑ j ∈ range (G - 1), a j := by
  rw [← sum_filter]
  refine sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => ha j
  have := (mem_filter.mp hj).2
  exact mem_range.mpr (by omega)

/-- Pronic evaluation of `tautSlope b N` on a window `[1, B₀)`. -/
theorem tautSlope_le {b : ℕ → ℤ} {N B₀ : ℕ} (hB₀ : 2 ≤ B₀) {Y : ℝ} (hY0 : 0 ≤ Y)
    (hnear : ∀ s : ℕ, 1 ≤ s → s < B₀ → |tautNear b N s - 1| ≤ (s : ℝ) * Y) :
    tautSlope b N ≤ 1 - 1 / (B₀ : ℝ) + Y * (1 + Real.log (B₀ : ℝ)) + tautMass b N / (B₀ : ℝ) := by
  have hsum := (isFakePrimeMeasure_pronic N).hasSum_saw (fun k => -(b k : ℝ) / k)
  have hobj : objective (fun k => -(b k : ℝ) / k) N = tautSlope b N := rfl
  rw [hobj] at hsum
  refine le_of_tendsto' hsum.tendsto_sum_nat fun n => ?_
  have hsaw : ∀ r, saw (fun k => -(b k : ℝ) / k) N r = tautNear b N r := fun _ => rfl
  simp only [hsaw]
  have hterm : ∀ j : ℕ, 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) * tautNear b N (j + 1) ≤
      (if j + 1 < B₀ then pronicStep' j else 0) +
      (if j + 1 < B₀ then Y * (1 / ((j : ℝ) + 2)) else 0) +
      tautMass b N * (if B₀ ≤ j + 1 then pronicStep' j else 0) := by
    intro j
    have hp := pronicStep'_nonneg j
    change pronicStep' j * tautNear b N (j + 1) ≤ _
    by_cases hj : j + 1 < B₀
    · rw [if_pos hj, if_pos hj, if_neg (by omega), mul_zero, add_zero]
      have hn := (abs_le.mp (hnear (j + 1) (by omega) hj)).2
      have h1 : tautNear b N (j + 1) ≤ 1 + ((j + 1 : ℕ) : ℝ) * Y := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hp
      have e : pronicStep' j * (1 + ((j + 1 : ℕ) : ℝ) * Y) =
          pronicStep' j + Y * (1 / ((j : ℝ) + 2)) := by
        rw [pronicStep']
        push_cast; field_simp
      linarith
    · rw [if_neg hj, if_neg hj, if_pos (by omega), zero_add, zero_add]
      exact (mul_comm _ _).trans_le
        (mul_le_mul_of_nonneg_right (abs_le.mp (abs_tautNear_le b N (j + 1))).2 hp)
  refine (sum_le_sum fun j _ => hterm j).trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
  have hA : ∑ j ∈ range n, (if j + 1 < B₀ then pronicStep' j else 0) ≤ 1 - 1 / (B₀ : ℝ) := by
    refine (sum_ite_lt_le'' pronicStep'_nonneg n B₀).trans_eq ?_
    rw [sum_range_pronicStep', Nat.cast_sub (by omega)]
    push_cast; congr 2; ring
  have hB : ∑ j ∈ range n, (if j + 1 < B₀ then Y * (1 / ((j : ℝ) + 2)) else 0) ≤
      Y * (1 + Real.log (B₀ : ℝ)) := by
    refine (sum_ite_lt_le'' (fun _ => by positivity) n B₀).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hY0
    have hH := harmonic_le_one_add_log B₀
    rw [harmonic_eq_sum_Icc] at hH
    push_cast at hH
    refine le_trans ?_ hH
    have hre : ∑ j ∈ range (B₀ - 1), 1 / ((j : ℝ) + 2) = ∑ i ∈ Ioc 1 B₀, ((i : ℝ))⁻¹ := by
      have hset : Ioc 1 B₀ = Ico 2 (B₀ + 1) := by ext x; simp [mem_Ioc, mem_Ico]; omega
      rw [hset, sum_Ico_eq_sum_range]
      have hn' : B₀ + 1 - 2 = B₀ - 1 := by omega
      rw [hn']
      refine sum_congr rfl fun _ _ => ?_
      push_cast; rw [one_div, add_comm]
    rw [hre]
    refine sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun _ _ _ => by positivity
    have := mem_Ioc.mp hi
    exact mem_Icc.mpr ⟨by omega, this.2⟩
  have hD : ∑ j ∈ range n, (if B₀ ≤ j + 1 then pronicStep' j else 0) ≤ 1 / (B₀ : ℝ) := by
    rw [← sum_filter]
    by_cases hnB : B₀ - 1 ≤ n
    · have hset : (range n).filter (fun j => B₀ ≤ j + 1) = Ico (B₀ - 1) n := by
        ext j; simp [mem_filter, mem_range, mem_Ico]; omega
      rw [hset, sum_Ico_pronicStep' hnB, Nat.cast_sub (by omega)]
      push_cast
      have e : (B₀ : ℝ) - 1 + 1 = B₀ := by ring
      rw [e]
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · have hset : (range n).filter (fun j => B₀ ≤ j + 1) = ∅ := by
        ext j; simp [mem_filter, mem_range]; omega
      rw [hset, sum_empty]; positivity
  have hD' := mul_le_mul_of_nonneg_left hD (tautMass_nonneg b N)
  have e : tautMass b N * (1 / (B₀ : ℝ)) = tautMass b N / (B₀ : ℝ) := by ring
  rw [e] at hD'
  linarith

/-! ### Part 2: Odd prime-power defects of a `4`-free smooth stencil -/

/-- Pairs `(q, e)` of odd primes `q ≥ 3` and exponents `e ≥ 1` with `q ^ e ≤ P_max`. -/
def oddPrimePowers (P_max : ℕ) : Finset (ℕ × ℕ) :=
  (((Icc 3 P_max).filter Nat.Prime) ×ˢ Icc 1 (Nat.log 2 P_max + 1)).filter
    fun x => x.1 ^ x.2 ≤ P_max

theorem mem_oddPrimePowers_iff {P_max : ℕ} {x : ℕ × ℕ} :
    x ∈ oddPrimePowers P_max ↔ 3 ≤ x.1 ∧ x.1.Prime ∧ 1 ≤ x.2 ∧ x.1 ^ x.2 ≤ P_max := by
  simp only [oddPrimePowers, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨⟨h3, -⟩, hp⟩, ⟨he1, -⟩⟩, hle⟩
    exact ⟨h3, hp, he1, hle⟩
  · rintro ⟨h3, hp, he1, hle⟩
    have hq_le : x.1 ≤ P_max := (Nat.le_self_pow (by omega) x.1).trans hle
    have h2e : 2 ^ x.2 ≤ P_max := (Nat.pow_le_pow_left hp.two_le x.2).trans hle
    have he_log : x.2 ≤ Nat.log 2 P_max + 1 :=
      (Nat.le_log_of_pow_le (by norm_num) h2e).trans (Nat.le_succ _)
    exact ⟨⟨⟨⟨h3, hq_le⟩, hp⟩, ⟨he1, he_log⟩⟩, hle⟩

/-- Defect `D_Q = ∑_{2 ≤ k ≤ N, Q ∣ k} |b(k)|` at a prime power `Q`. -/
def tautDefect (b : ℕ → ℤ) (N Q : ℕ) : ℕ :=
  ∑ k ∈ Icc 2 N, if Q ∣ k then (b k).natAbs else 0

theorem cast_tautDefect (b : ℕ → ℤ) (N Q : ℕ) :
    (tautDefect b N Q : ℝ) = ∑ k ∈ Icc 2 N, if Q ∣ k then |(b k : ℝ)| else 0 := by
  rw [tautDefect]
  push_cast
  refine sum_congr rfl fun k _ => ?_
  split_ifs
  · rw [Nat.cast_natAbs, Int.cast_abs]
  · rfl

/-- Every integer `k ≤ N` is divisible by at most `(log₂ N)²` prime powers, so the sum of all
odd prime-power defects is at most `(log₂ N + 1)² · tautMass b N`. -/
theorem sum_tautDefect_le (b : ℕ → ℤ) (N P_max : ℕ) :
    ∑ x ∈ oddPrimePowers P_max, (tautDefect b N (x.1 ^ x.2) : ℝ) ≤
      ((Nat.log 2 N : ℝ) + 1) ^ 2 * tautMass b N := by
  simp only [cast_tautDefect]
  rw [sum_comm]
  have hterm : ∀ k ∈ Icc 2 N,
      (∑ x ∈ oddPrimePowers P_max, if x.1 ^ x.2 ∣ k then |(b k : ℝ)| else 0) ≤
        ((Nat.log 2 N : ℝ) + 1) ^ 2 * |(b k : ℝ)| := by
    intro k hk
    obtain ⟨hk2, hkN⟩ := mem_Icc.mp hk
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have hsub : (oddPrimePowers P_max).filter (fun x => x.1 ^ x.2 ∣ k) ⊆
        k.primeFactors ×ˢ Icc 1 (Nat.log 2 N) := by
      intro x hx
      obtain ⟨hx_mem, hdvd⟩ := mem_filter.mp hx
      obtain ⟨_, hp, he1, -⟩ := mem_oddPrimePowers_iff.mp hx_mem
      have hqdvd : x.1 ∣ k := (dvd_pow_self x.1 (by omega)).trans hdvd
      have h2e : 2 ^ x.2 ≤ N :=
        (Nat.pow_le_pow_left hp.two_le x.2).trans ((Nat.le_of_dvd (by omega) hdvd).trans hkN)
      exact mem_product.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨hp, hqdvd, by omega⟩,
         mem_Icc.mpr ⟨he1, Nat.le_log_of_pow_le (by norm_num) h2e⟩⟩
    have hpf : k.primeFactors.card ≤ Nat.log 2 N := by
      have hdvd : ∏ q ∈ k.primeFactors, q ∣ k :=
        Finset.prod_primes_dvd k
          (fun _ hq => (Nat.prime_of_mem_primeFactors hq).prime)
          (fun _ hq => Nat.dvd_of_mem_primeFactors hq)
      have hpow : 2 ^ k.primeFactors.card ≤ ∏ q ∈ k.primeFactors, q :=
        Finset.pow_card_le_prod k.primeFactors id 2
          fun _ hq => (Nat.prime_of_mem_primeFactors hq).two_le
      exact Nat.le_log_of_pow_le (by norm_num) (hpow.trans ((Nat.le_of_dvd (by omega) hdvd).trans hkN))
    have hcard : ((oddPrimePowers P_max).filter (fun x => x.1 ^ x.2 ∣ k)).card ≤
        (Nat.log 2 N + 1) ^ 2 := by
      have hc1 := card_le_card hsub
      rw [card_product, Nat.card_Icc] at hc1
      have hc2 : k.primeFactors.card * (Nat.log 2 N + 1 - 1) ≤ (Nat.log 2 N + 1) ^ 2 := by
        have : Nat.log 2 N + 1 - 1 = Nat.log 2 N := by omega
        rw [this]; nlinarith
      exact hc1.trans hc2
    exact_mod_cast hcard
  exact (sum_le_sum hterm).trans_eq (by rw [← mul_sum]; rfl)

/-- Because `b 2 = -1` contributes `+(r mod 2) / 2 ≥ 0` and every active `k ≥ 3` with `¬ 4 ∣ k`
is divisible by an odd prime power `≤ P_max`, `tautNear b N r ≥ -∑_Q D_Q` for every `r`. -/
theorem neg_sum_tautDefect_le_tautNear {b : ℕ → ℤ} {N P_max : ℕ}
    (hN : 2 ≤ N) (hb2 : b 2 = -1)
    (hb_smooth : ∀ k : ℕ, 2 ≤ k → k ≤ N → b k ≠ 0 → ¬ 4 ∣ k ∧
      ∀ q e : ℕ, q.Prime → 1 ≤ e → q ^ e ∣ k → q ^ e ≤ P_max)
    (r : ℕ) :
    -(∑ x ∈ oddPrimePowers P_max, (tautDefect b N (x.1 ^ x.2) : ℝ)) ≤ tautNear b N r := by
  have hsplit : Icc 2 N = insert 2 (Icc 3 N) := by
    ext k; simp [mem_Icc, mem_insert]; omega
  have h2not : (2 : ℕ) ∉ Icc 3 N := by simp
  rw [tautNear, hsplit, sum_insert h2not, hb2]
  have h2_nn : (0 : ℝ) ≤ (-((-1 : ℤ) : ℝ) / (2 : ℕ)) * ((r % 2 : ℕ) : ℝ) := by
    push_cast; positivity
  have hterm : ∀ k ∈ Icc 3 N,
      -(∑ x ∈ oddPrimePowers P_max, if x.1 ^ x.2 ∣ k then |(b k : ℝ)| else 0) ≤
        (-(b k : ℝ) / k) * ((r % k : ℕ) : ℝ) := by
    intro k hk
    obtain ⟨hk3, hkN⟩ := mem_Icc.mp hk
    have hnn : ∀ x ∈ oddPrimePowers P_max,
        (0 : ℝ) ≤ if x.1 ^ x.2 ∣ k then |(b k : ℝ)| else 0 :=
      fun _ _ => by split_ifs; exact abs_nonneg _; exact le_rfl
    by_cases hbk : b k = 0
    · simp [hbk]
    · obtain ⟨hn4, hpp⟩ := hb_smooth k (by omega) hkN hbk
      have hndvd2 : ¬ k ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
      rw [Nat.dvd_iff_prime_pow_dvd_dvd] at hndvd2
      push Not at hndvd2
      obtain ⟨q, e, hq, hqek, hqe2⟩ := hndvd2
      have he1 : 1 ≤ e := by
        by_contra he0
        have : e = 0 := by omega
        subst this; exact hqe2 (by norm_num)
      have hq3 : 3 ≤ q := by
        have hq2 := hq.two_le
        by_contra hlt3
        have hq_eq : q = 2 := by omega
        subst hq_eq
        have he2 : 2 ≤ e := by
          by_contra hlt2
          have : e = 1 := by omega
          subst this; exact hqe2 (by norm_num)
        exact hn4 ((show 4 ∣ 2 ^ e from pow_dvd_pow 2 he2).trans hqek)
      have hmem : (q, e) ∈ oddPrimePowers P_max :=
        mem_oddPrimePowers_iff.mpr ⟨hq3, hq, he1, hpp q e hq he1 hqek⟩
      have hsingle := single_le_sum hnn hmem
      simp only [hqek, ↓reduceIte] at hsingle
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hmod : ((r % k : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.mod_lt r (by omega)).le
      have habs : |(-(b k : ℝ) / k) * ((r % k : ℕ) : ℝ)| ≤ |(b k : ℝ)| := by
        rw [abs_mul, abs_div, abs_neg, abs_of_pos hkR, Nat.abs_cast]
        calc |(b k : ℝ)| / k * ((r % k : ℕ) : ℝ) ≤ |(b k : ℝ)| / k * k := by gcongr
          _ = |(b k : ℝ)| := by field_simp
      linarith [(abs_le.mp habs).1, hsingle]
  have hsum3 : -(∑ x ∈ oddPrimePowers P_max, (tautDefect b N (x.1 ^ x.2) : ℝ)) ≤
      ∑ k ∈ Icc 3 N, (-(b k : ℝ) / k) * ((r % k : ℕ) : ℝ) := by
    have hsub_sum : ∑ x ∈ oddPrimePowers P_max,
        (∑ k ∈ Icc 3 N, if x.1 ^ x.2 ∣ k then |(b k : ℝ)| else 0) ≤
        ∑ x ∈ oddPrimePowers P_max, (tautDefect b N (x.1 ^ x.2) : ℝ) := by
      refine sum_le_sum fun x _ => ?_
      rw [cast_tautDefect]
      refine sum_le_sum_of_subset_of_nonneg
        (fun k hk => by obtain ⟨hk3, hkN⟩ := mem_Icc.mp hk; exact mem_Icc.mpr ⟨by omega, hkN⟩)
        fun _ _ _ => ?_
      split_ifs; exact abs_nonneg _; exact le_rfl
    have hneg : -(∑ x ∈ oddPrimePowers P_max, (tautDefect b N (x.1 ^ x.2) : ℝ)) ≤
        ∑ k ∈ Icc 3 N, -(∑ x ∈ oddPrimePowers P_max, if x.1 ^ x.2 ∣ k then |(b k : ℝ)| else 0) := by
      rw [sum_neg_distrib, ← sum_comm]
      linarith
    exact hneg.trans (sum_le_sum hterm)
  linarith

/-- If `h ≤ r` and `2 ∣ r - h`, only odd prime powers failing to divide `r - h` can separate
`tautNear b N r` from `tautNear b N h`. -/
theorem abs_tautNear_sub_le_tautDefect {b : ℕ → ℤ} {N P_max r h : ℕ}
    (hb_smooth : ∀ k : ℕ, 2 ≤ k → k ≤ N → b k ≠ 0 → ¬ 4 ∣ k ∧
      ∀ q e : ℕ, q.Prime → 1 ≤ e → q ^ e ∣ k → q ^ e ≤ P_max)
    (hhr : h ≤ r) (h2 : 2 ∣ r - h) :
    |tautNear b N r - tautNear b N h| ≤
      ∑ x ∈ oddPrimePowers P_max,
        if x.1 ^ x.2 ∣ r - h then 0 else (tautDefect b N (x.1 ^ x.2) : ℝ) := by
  have hterm : ∀ k ∈ Icc 2 N,
      |(-(b k : ℝ) / k) * ((r % k : ℕ) : ℝ) - (-(b k : ℝ) / k) * ((h % k : ℕ) : ℝ)| ≤
        ∑ x ∈ oddPrimePowers P_max,
          if x.1 ^ x.2 ∣ r - h then 0 else (if x.1 ^ x.2 ∣ k then |(b k : ℝ)| else 0) := by
    intro k hk
    obtain ⟨hk2, hkN⟩ := mem_Icc.mp hk
    have hnn : ∀ x ∈ oddPrimePowers P_max, (0 : ℝ) ≤
        if x.1 ^ x.2 ∣ r - h then 0 else (if x.1 ^ x.2 ∣ k then |(b k : ℝ)| else 0) :=
      fun _ _ => by split_ifs; exact le_rfl; exact abs_nonneg _; exact le_rfl
    by_cases hdvd : k ∣ r - h
    · have hm : h % k = r % k := (Nat.modEq_iff_dvd' hhr).mpr hdvd
      rw [hm, sub_self, abs_zero]
      exact sum_nonneg hnn
    by_cases hbk : b k = 0
    · rw [hbk]
      simp only [Int.cast_zero, neg_zero, zero_div, zero_mul, sub_self, abs_zero]
      exact sum_nonneg fun _ _ => by split_ifs <;> positivity
    obtain ⟨hn4, hpp⟩ := hb_smooth k hk2 hkN hbk
    rw [Nat.dvd_iff_prime_pow_dvd_dvd] at hdvd
    push Not at hdvd
    obtain ⟨q, e, hq, hqek, hqer⟩ := hdvd
    have he1 : 1 ≤ e := by
      by_contra he0
      have : e = 0 := by omega
      subst this; exact hqer (by simp)
    have hq3 : 3 ≤ q := by
      have hq2 := hq.two_le
      by_contra hlt3
      have hq_eq : q = 2 := by omega
      subst hq_eq
      have he_eq1 : e = 1 := by
        by_contra hne1
        have he2 : 2 ≤ e := by omega
        exact hn4 ((show 4 ∣ 2 ^ e from pow_dvd_pow 2 he2).trans hqek)
      subst he_eq1
      exact hqer (by simpa using h2)
    have hmem : (q, e) ∈ oddPrimePowers P_max :=
      mem_oddPrimePowers_iff.mpr ⟨hq3, hq, he1, hpp q e hq he1 hqek⟩
    have hsingle := single_le_sum hnn hmem
    simp only [hqer, ↓reduceIte, hqek] at hsingle
    refine le_trans ?_ hsingle
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hr1 : ((r % k : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.mod_lt r (by omega)).le
    have hh1 : ((h % k : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.mod_lt h (by omega)).le
    have hr0 : (0 : ℝ) ≤ ((r % k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hh0 : (0 : ℝ) ≤ ((h % k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hdiff : |((r % k : ℕ) : ℝ) - ((h % k : ℕ) : ℝ)| ≤ k := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [← mul_sub, abs_mul, abs_div, abs_neg, abs_of_pos hkR]
    calc |(b k : ℝ)| / k * |((r % k : ℕ) : ℝ) - ((h % k : ℕ) : ℝ)|
        ≤ |(b k : ℝ)| / k * k := by gcongr
      _ = |(b k : ℝ)| := by field_simp
  rw [tautNear, tautNear, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans_eq ?_)
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  split_ifs
  · simp
  · rw [cast_tautDefect]

/-! ### Part 3: Iterated Bertrand prime pool, Hamming squares, and subset-product CRT ramp -/

/-- Prime pool `{p prime : W < p ≤ 2^S W}` obtained across `S` dyadic octaves. -/
def bertrandPrimes (W S : ℕ) : Finset ℕ :=
  (Ioc W (2 ^ S * W)).filter Nat.Prime

theorem mem_bertrandPrimes {W S p : ℕ} :
    p ∈ bertrandPrimes W S ↔ (W < p ∧ p ≤ 2 ^ S * W) ∧ p.Prime := by
  simp [bertrandPrimes, mem_filter, mem_Ioc]

/-- Iterated Bertrand's postulate gives at least `S` primes in `(W, 2^S W]` for every `W ≥ 1`. -/
theorem le_card_bertrandPrimes {W : ℕ} (hW : 1 ≤ W) (S : ℕ) :
    S ≤ (bertrandPrimes W S).card := by
  induction S with
  | zero => exact Nat.zero_le _
  | succ S ih =>
    have hpos : 2 ^ S * W ≠ 0 := (Nat.mul_pos (pow_pos (by norm_num) S) hW).ne'
    obtain ⟨p, hp, hgt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ S * W) hpos
    have hnot : p ∉ bertrandPrimes W S := by
      intro hm; have := (mem_bertrandPrimes.mp hm).1.2; omega
    have hsub : insert p (bertrandPrimes W S) ⊆ bertrandPrimes W (S + 1) := by
      intro q hq
      rcases mem_insert.mp hq with rfl | hq'
      · refine mem_bertrandPrimes.mpr ⟨⟨?_, ?_⟩, hp⟩
        · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left W (pow_pos (by norm_num) S)) hgt
        · rw [pow_succ']; linarith
      · obtain ⟨⟨hq1, hq2⟩, hqp⟩ := mem_bertrandPrimes.mp hq'
        refine mem_bertrandPrimes.mpr ⟨⟨hq1, hq2.trans ?_⟩, hqp⟩
        exact Nat.mul_le_mul_right W (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ S))
    have hcard := card_le_card hsub
    rw [card_insert_of_notMem hnot] at hcard
    omega

/-- Cluster prime pool `P_W \ {q}` avoiding the base prime `q` of `Q = q^e`. -/
def clusterPrimes (W S q : ℕ) : Finset ℕ :=
  (bertrandPrimes W S).erase q

theorem clusterPrimes_subset (W S q : ℕ) : clusterPrimes W S q ⊆ bertrandPrimes W S :=
  erase_subset q (bertrandPrimes W S)

theorem le_card_clusterPrimes {W : ℕ} (hW : 1 ≤ W) (S q : ℕ) :
    S - 1 ≤ (clusterPrimes W S q).card := by
  have h := le_card_bertrandPrimes hW S
  unfold clusterPrimes
  by_cases hq : q ∈ bertrandPrimes W S
  · rw [card_erase_of_mem hq]; omega
  · rw [erase_eq_of_notMem hq]; omega

/-- Dyadic padding exponent `b_Q = ⌊log₂(K / (2^{2S} W² Q))⌋` for a prime power `Q`. -/
def hammingExp (K W S Q : ℕ) : ℕ :=
  Nat.log 2 (K / (2 ^ (2 * S) * W ^ 2 * Q))

/-- Single-prime base modulus `G_Q(p) = 2^{b_Q} p Q`. -/
def hammingBase (K W S Q p : ℕ) : ℕ :=
  2 ^ hammingExp K W S Q * p * Q

/-- Bipartite Hamming-square letter `L_Q(p₁, p₂) = 2^{b_Q} p₁ p₂ Q`. -/
def hammingLetter (K W S Q p₁ p₂ : ℕ) : ℕ :=
  2 ^ hammingExp K W S Q * p₁ * p₂ * Q

private lemma hammingExp_pos {K W S Q P_max : ℕ} (hW : 2 ≤ W) (hQ : 1 ≤ Q) (hQP : Q ≤ P_max)
    (hK : 2 ^ (2 * S + 2) * W ^ 2 * (P_max + 1) ≤ K) :
    1 ≤ hammingExp K W S Q := by
  unfold hammingExp
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  rw [pow_one]
  have hpos : 0 < 2 ^ (2 * S) * W ^ 2 * Q := by positivity
  rw [Nat.le_div_iff_mul_le hpos]
  have hle1 : Q ≤ P_max + 1 := by omega
  have hle2 : 2 * (2 ^ (2 * S) * W ^ 2 * Q) ≤ 2 ^ (2 * S + 2) * W ^ 2 * (P_max + 1) := by
    calc 2 * (2 ^ (2 * S) * W ^ 2 * Q)
        ≤ 4 * (2 ^ (2 * S) * W ^ 2 * (P_max + 1)) := by
          have : 2 ^ (2 * S) * W ^ 2 * Q ≤ 2 ^ (2 * S) * W ^ 2 * (P_max + 1) :=
            Nat.mul_le_mul_left _ hle1
          linarith
      _ = 2 ^ (2 * S + 2) * W ^ 2 * (P_max + 1) := by rw [pow_add]; norm_num; ring
  exact hle2.trans hK

private lemma hammingLetter_bounds {K W S Q P_max p₁ p₂ : ℕ}
    (hW : 2 ≤ W) (hQ : 1 ≤ Q) (hQP : Q ≤ P_max)
    (hK : 2 ^ (2 * S + 2) * W ^ 2 * (P_max + 1) ≤ K)
    (hp₁ : p₁ ∈ bertrandPrimes W S) (hp₂ : p₂ ∈ bertrandPrimes W S) :
    2 ≤ hammingLetter K W S Q p₁ p₂ ∧
    hammingLetter K W S Q p₁ p₂ ≤ K ∧
    K < 2 ^ (2 * S + 1) * hammingLetter K W S Q p₁ p₂ ∧
    K < (2 ^ (2 * S + 1) * W) * hammingBase K W S Q p₁ := by
  obtain ⟨⟨hp₁_gt, hp₁_le⟩, -⟩ := mem_bertrandPrimes.mp hp₁
  obtain ⟨⟨hp₂_gt, hp₂_le⟩, -⟩ := mem_bertrandPrimes.mp hp₂
  have hb1 := hammingExp_pos hW hQ hQP hK
  set D₀ := 2 ^ (2 * S) * W ^ 2 * Q
  have hD₀_pos : 0 < D₀ := by positivity
  have hdiv_ne : K / D₀ ≠ 0 := by
    have : 1 ≤ Nat.log 2 (K / D₀) := hb1
    intro h0; simp [h0] at this
  have hpow_le : 2 ^ hammingExp K W S Q ≤ K / D₀ := Nat.pow_log_le_self 2 hdiv_ne
  have hpow_gt : K / D₀ < 2 * 2 ^ hammingExp K W S Q := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (K / D₀)
    rw [pow_succ'] at h; exact h
  have hp_prod_le : p₁ * p₂ * Q ≤ D₀ := by
    calc p₁ * p₂ * Q ≤ (2 ^ S * W) * (2 ^ S * W) * Q :=
          Nat.mul_le_mul_right Q (Nat.mul_le_mul hp₁_le hp₂_le)
      _ = (2 ^ S * 2 ^ S) * W ^ 2 * Q := by ring
      _ = 2 ^ (2 * S) * W ^ 2 * Q := by rw [← pow_add, two_mul]
  have hL_ge2 : 2 ≤ hammingLetter K W S Q p₁ p₂ := by
    have h2b : 2 ≤ 2 ^ hammingExp K W S Q := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ hammingExp K W S Q := Nat.pow_le_pow_right (by norm_num) hb1
    have hpQ : 1 ≤ p₁ * p₂ * Q := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hQ
    calc 2 = 2 * 1 := (mul_one 2).symm
      _ ≤ 2 ^ hammingExp K W S Q * (p₁ * p₂ * Q) := Nat.mul_le_mul h2b hpQ
      _ = hammingLetter K W S Q p₁ p₂ := by unfold hammingLetter; ring
  have hL_le : hammingLetter K W S Q p₁ p₂ ≤ K := by
    unfold hammingLetter
    calc 2 ^ hammingExp K W S Q * p₁ * p₂ * Q
        = 2 ^ hammingExp K W S Q * (p₁ * p₂ * Q) := by ring
      _ ≤ (K / D₀) * D₀ := Nat.mul_le_mul hpow_le hp_prod_le
      _ ≤ K := Nat.div_mul_le_self K D₀
  have hK_lt_D₀ : K < D₀ * (2 * 2 ^ hammingExp K W S Q) := by
    calc K < D₀ * (K / D₀ + 1) := Nat.lt_mul_div_succ K hD₀_pos
      _ ≤ D₀ * (2 * 2 ^ hammingExp K W S Q) := Nat.mul_le_mul_left D₀ (by omega)
  refine ⟨hL_ge2, hL_le, ?_, ?_⟩
  · unfold hammingLetter
    have hW_p : W ^ 2 ≤ p₁ * p₂ := by
      have : W * W ≤ p₁ * p₂ := Nat.mul_le_mul (by omega) (by omega)
      simpa [sq] using this
    calc K < (2 ^ (2 * S) * W ^ 2 * Q) * (2 * 2 ^ hammingExp K W S Q) := hK_lt_D₀
      _ = 2 ^ (2 * S + 1) * 2 ^ hammingExp K W S Q * Q * W ^ 2 := by rw [pow_succ]; ring
      _ ≤ 2 ^ (2 * S + 1) * 2 ^ hammingExp K W S Q * Q * (p₁ * p₂) :=
          Nat.mul_le_mul_left _ hW_p
      _ = 2 ^ (2 * S + 1) * (2 ^ hammingExp K W S Q * p₁ * p₂ * Q) := by ring
  · unfold hammingBase
    have hW_p1 : W ≤ p₁ := by omega
    calc K < (2 ^ (2 * S) * W ^ 2 * Q) * (2 * 2 ^ hammingExp K W S Q) := hK_lt_D₀
      _ = (2 ^ (2 * S + 1) * W * 2 ^ hammingExp K W S Q * Q) * W := by rw [pow_succ]; ring
      _ ≤ (2 ^ (2 * S + 1) * W * 2 ^ hammingExp K W S Q * Q) * p₁ :=
          Nat.mul_le_mul_left _ hW_p1
      _ = (2 ^ (2 * S + 1) * W) * (2 ^ hammingExp K W S Q * p₁ * Q) := by ring

private lemma hamming_mod_align {K W S Q p₁ p₂ B₀ r : ℕ}
    (hB₁ : B₀ < hammingBase K W S Q p₁) (hB₂ : B₀ < hammingBase K W S Q p₂)
    (hsmall : r % hammingLetter K W S Q p₁ p₂ < B₀) :
    r % hammingBase K W S Q p₁ = r % hammingLetter K W S Q p₁ p₂ ∧
    r % hammingBase K W S Q p₂ = r % hammingLetter K W S Q p₁ p₂ := by
  have hdvd₁ : hammingBase K W S Q p₁ ∣ hammingLetter K W S Q p₁ p₂ :=
    ⟨p₂, by unfold hammingBase hammingLetter; ring⟩
  have hdvd₂ : hammingBase K W S Q p₂ ∣ hammingLetter K W S Q p₁ p₂ :=
    ⟨p₁, by unfold hammingBase hammingLetter; ring⟩
  refine ⟨?_, ?_⟩
  · have h1 : (r % hammingLetter K W S Q p₁ p₂) % hammingBase K W S Q p₁ =
        r % hammingBase K W S Q p₁ := (Nat.mod_modEq r _).of_dvd hdvd₁
    rw [← h1, Nat.mod_eq_of_lt (hsmall.trans hB₁)]
  · have h2 : (r % hammingLetter K W S Q p₁ p₂) % hammingBase K W S Q p₂ =
        r % hammingBase K W S Q p₂ := (Nat.mod_modEq r _).of_dvd hdvd₂
    rw [← h2, Nat.mod_eq_of_lt (hsmall.trans hB₂)]

/-- Majority-good rows `p₁ ∈ C` having more than `|C| / 2` small-residue columns `p₂ ∈ C`. -/
private def alignedRows (K W S Q B₀ r : ℕ) (C : Finset ℕ) : Finset ℕ :=
  C.filter fun p₁ =>
    C.card < 2 * (C.filter fun p₂ => r % hammingLetter K W S Q p₁ p₂ < B₀).card

/-- Row/column majority connectedness on a bipartite Hamming square: if fewer than
`|C|² / (16 M₀)` pairs in `C ×ˢ C` have residue `≥ B₀`, then `alignedRows` misses very few primes
of `P` and every row in `alignedRows` shares a single residue `h < B₀` modulo `hammingBase`. -/
private lemma alignedRows_spec {K W S Q B₀ r M₀ q : ℕ} {P : Finset ℕ}
    (hM₀ : 2 ≤ M₀) (hC_pos : 0 < (P.erase q).card)
    (hBase : ∀ p ∈ P.erase q, B₀ < hammingBase K W S Q p)
    (hb1 : 1 ≤ hammingExp K W S Q)
    (halign : 16 * M₀ *
      (((P.erase q) ×ˢ (P.erase q)).filter
        fun p => B₀ ≤ r % hammingLetter K W S Q p.1 p.2).card <
      (P.erase q).card ^ 2) :
    let C := P.erase q
    let R := alignedRows K W S Q B₀ r C
    R ⊆ P ∧
    8 * M₀ * (P \ R).card ≤ P.card + 8 * M₀ - 1 ∧
    ∃ h < B₀, 2 ∣ r - h ∧ Q ∣ r - h ∧ ∀ p ∈ R, p ∣ r - h := by
  intro C R
  have hC_sub : C ⊆ P := erase_subset q P
  have hR_sub_C : R ⊆ C := filter_subset _ _
  have hR_sub_P : R ⊆ P := hR_sub_C.trans hC_sub
  let goodC : ℕ → Finset ℕ := fun p₁ =>
    C.filter fun p₂ => r % hammingLetter K W S Q p₁ p₂ < B₀
  let badC : ℕ → Finset ℕ := fun p₁ =>
    C.filter fun p₂ => ¬ r % hammingLetter K W S Q p₁ p₂ < B₀
  have hcol_part : ∀ p₁ : ℕ, (goodC p₁).card + (badC p₁).card = C.card :=
    fun p₁ => card_filter_add_card_filter_not _
  have hbad_sum : (((C ×ˢ C).filter
      fun p => B₀ ≤ r % hammingLetter K W S Q p.1 p.2).card) =
      ∑ p₁ ∈ C, (badC p₁).card := by
    have hcongr : (C ×ˢ C).filter (fun p => B₀ ≤ r % hammingLetter K W S Q p.1 p.2) =
        (C ×ˢ C).filter (fun p => ¬ r % hammingLetter K W S Q p.1 p.2 < B₀) :=
      filter_congr fun _ _ => not_lt.symm
    rw [hcongr, card_filter, sum_product]
    exact sum_congr rfl fun p₁ _ => (card_filter _ C).symm
  set badR := C.filter fun p₁ => ¬ C.card < 2 * (goodC p₁).card
  have hrow_part : R.card + badR.card = C.card := card_filter_add_card_filter_not _
  have hbadR_mul : badR.card * C.card ≤ 2 * ∑ p₁ ∈ C, (badC p₁).card := by
    have hterm : ∀ p₁ ∈ badR, C.card ≤ 2 * (badC p₁).card := by
      intro p₁ hp₁
      have hle : 2 * (goodC p₁).card ≤ C.card := not_lt.mp (mem_filter.mp hp₁).2
      have hp := hcol_part p₁
      omega
    calc badR.card * C.card = ∑ _p₁ ∈ badR, C.card := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ p₁ ∈ badR, 2 * (badC p₁).card := sum_le_sum hterm
      _ ≤ ∑ p₁ ∈ C, 2 * (badC p₁).card :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.zero_le _
      _ = 2 * ∑ p₁ ∈ C, (badC p₁).card := (mul_sum _ _ _).symm
  have hbadR_lt : 8 * M₀ * badR.card < C.card := by
    have hmul : (8 * M₀ * badR.card) * C.card < C.card * C.card := by
      calc (8 * M₀ * badR.card) * C.card
          = 8 * M₀ * (badR.card * C.card) := by ring
        _ ≤ 8 * M₀ * (2 * ∑ p₁ ∈ C, (badC p₁).card) := Nat.mul_le_mul_left _ hbadR_mul
        _ = 16 * M₀ * (((C ×ˢ C).filter
              fun p => B₀ ≤ r % hammingLetter K W S Q p.1 p.2).card) := by
            rw [hbad_sum]; ring
        _ < C.card ^ 2 := halign
        _ = C.card * C.card := sq C.card
    exact Nat.lt_of_mul_lt_mul_right hmul
  have hsdiff_sub : P \ R ⊆ insert q badR := by
    intro p hp
    obtain ⟨hpP, hpR⟩ := mem_sdiff.mp hp
    by_cases hpq : p = q
    · exact hpq ▸ mem_insert_self q badR
    · have hpC : p ∈ C := mem_erase.mpr ⟨hpq, hpP⟩
      have hngood : ¬ C.card < 2 * (goodC p).card := fun hg => hpR (mem_filter.mpr ⟨hpC, hg⟩)
      exact mem_insert_of_mem (mem_filter.mpr ⟨hpC, hngood⟩)
  have hsdiff_card : (P \ R).card ≤ badR.card + 1 :=
    (card_le_card hsdiff_sub).trans (card_insert_le q badR)
  have hC_le_P : C.card ≤ P.card := card_le_card hC_sub
  have hsdiff_bd : 8 * M₀ * (P \ R).card ≤ P.card + 8 * M₀ - 1 := by
    have h1 : 8 * M₀ * (P \ R).card ≤ 8 * M₀ * (badR.card + 1) :=
      Nat.mul_le_mul_left _ hsdiff_card
    have h2 : 8 * M₀ * (badR.card + 1) = 8 * M₀ * badR.card + 8 * M₀ := by ring
    omega
  have hR_ne : R.Nonempty := by
    refine Finset.card_pos.mp ?_
    have : badR.card < C.card := by nlinarith
    omega
  set p₀ := R.min' hR_ne
  have hp₀_mem : p₀ ∈ R := min'_mem R hR_ne
  set h := r % hammingBase K W S Q p₀
  have hp₀_lt_B₀ : h < B₀ := by
    obtain ⟨hp₀C, hp₀_maj⟩ := mem_filter.mp hp₀_mem
    change C.card < 2 * (goodC p₀).card at hp₀_maj
    have hgood_ne : (goodC p₀).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p₂, hp₂_good⟩ := hgood_ne
    obtain ⟨hp₂C, hsmall⟩ := mem_filter.mp hp₂_good
    have hal := hamming_mod_align (hBase p₀ hp₀C) (hBase p₂ hp₂C) hsmall
    dsimp [h]
    rwa [hal.1]
  have hall_eq : ∀ p₁ ∈ R, r % hammingBase K W S Q p₁ = h := by
    intro p₁ hp₁
    obtain ⟨hp₀C, hp₀_maj⟩ := mem_filter.mp hp₀_mem
    obtain ⟨hp₁C, hp₁_maj⟩ := mem_filter.mp hp₁
    change C.card < 2 * (goodC p₀).card at hp₀_maj
    change C.card < 2 * (goodC p₁).card at hp₁_maj
    have hunion_le : (goodC p₀ ∪ goodC p₁).card ≤ C.card :=
      card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
    have hinter_card := card_union_add_card_inter (goodC p₀) (goodC p₁)
    have hinter_ne : (goodC p₀ ∩ goodC p₁).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p₂, hp₂_inter⟩ := hinter_ne
    obtain ⟨hp₂_0, hp₂_1⟩ := mem_inter.mp hp₂_inter
    obtain ⟨hp₂C, hsm₀⟩ := mem_filter.mp hp₂_0
    obtain ⟨_, hsm₁⟩ := mem_filter.mp hp₂_1
    have hal₀ := hamming_mod_align (hBase p₀ hp₀C) (hBase p₂ hp₂C) hsm₀
    have hal₁ := hamming_mod_align (hBase p₁ hp₁C) (hBase p₂ hp₂C) hsm₁
    dsimp [h]
    rw [hal₁.1, ← hal₁.2, hal₀.2, ← hal₀.1]
  have hdvd_base : ∀ p₁ ∈ R, hammingBase K W S Q p₁ ∣ r - h := by
    intro p₁ hp₁
    rw [← hall_eq p₁ hp₁]
    exact (Nat.modEq_iff_dvd' (Nat.mod_le r _)).mp (Nat.mod_modEq r _)
  have hdvd_p₀ := hdvd_base p₀ hp₀_mem
  have h2_dvd : 2 ∣ r - h := by
    have h2_exp : 2 ∣ 2 ^ hammingExp K W S Q := dvd_pow_self 2 (by omega)
    have h2_base : 2 ^ hammingExp K W S Q ∣ hammingBase K W S Q p₀ :=
      ⟨p₀ * Q, by unfold hammingBase; ring⟩
    exact dvd_trans (dvd_trans h2_exp h2_base) hdvd_p₀
  have hQ_dvd : Q ∣ r - h :=
    dvd_trans ⟨2 ^ hammingExp K W S Q * p₀, by unfold hammingBase; ring⟩ hdvd_p₀
  have hp_dvd : ∀ p ∈ R, p ∣ r - h := fun p hp =>
    dvd_trans ⟨2 ^ hammingExp K W S Q * Q, by unfold hammingBase; ring⟩ (hdvd_base p hp)
  exact ⟨hR_sub_P, hsdiff_bd, h, hp₀_lt_B₀, h2_dvd, hQ_dvd, hp_dvd⟩

/-- Combinatorial half-retention for `m`-subsets when `2 * |P \ R| * m ≤ |P|`. -/
private lemma powersetCard_half_subset {α : Type*} [DecidableEq α]
    {P R : Finset α} {m : ℕ} (hm1 : 1 ≤ m) (hmP : m ≤ P.card)
    (hbad : 2 * (P \ R).card * m ≤ P.card) :
    (P.powersetCard m).card ≤ 2 * ((P.powersetCard m).filter (· ⊆ R)).card := by
  have hP_pos : 0 < P.card := lt_of_lt_of_le Nat.zero_lt_one (hm1.trans hmP)
  set goodF := (P.powersetCard m).filter (· ⊆ R)
  set badF := (P.powersetCard m).filter (fun A => ¬ A ⊆ R)
  have hpart : goodF.card + badF.card = (P.powersetCard m).card :=
    card_filter_add_card_filter_not (· ⊆ R)
  have hcov : badF ⊆ (P \ R).biUnion (fun x => (P.powersetCard m).filter ({x} ⊆ ·)) := by
    intro A hA
    obtain ⟨hAP, hnR⟩ := mem_filter.mp hA
    obtain ⟨hA_sub, _⟩ := mem_powersetCard.mp hAP
    obtain ⟨x, hxA, hxR⟩ := Finset.not_subset.mp hnR
    exact mem_biUnion.mpr ⟨x, mem_sdiff.mpr ⟨hA_sub hxA, hxR⟩,
      mem_filter.mpr ⟨hAP, singleton_subset_iff.mpr hxA⟩⟩
  have hbad_card : badF.card ≤ (P \ R).card * (P.card - 1).choose (m - 1) := by
    refine (card_le_card hcov).trans (card_biUnion_le.trans ?_)
    have hfib : ∀ x ∈ P \ R,
        ((P.powersetCard m).filter ({x} ⊆ ·)).card ≤ (P.card - 1).choose (m - 1) := by
      intro x hx
      have hxP : x ∈ P := (mem_sdiff.mp hx).1
      set F := (P.powersetCard m).filter ({x} ⊆ ·)
      have hinj : Set.InjOn (fun A : Finset α => A.erase x) F := by
        intro A₁ hA₁ A₂ hA₂ heq
        dsimp only at heq
        have hx₁ : x ∈ A₁ := singleton_subset_iff.mp (mem_filter.mp hA₁).2
        have hx₂ : x ∈ A₂ := singleton_subset_iff.mp (mem_filter.mp hA₂).2
        rw [← insert_erase hx₁, ← insert_erase hx₂, heq]
      have himg : F.image (fun A => A.erase x) ⊆ (P.erase x).powersetCard (m - 1) := by
        intro B hB
        rcases mem_image.mp hB with ⟨A, hAF, rfl⟩
        obtain ⟨hAP, hxA⟩ := mem_filter.mp hAF
        obtain ⟨hA_sub, hA_card⟩ := mem_powersetCard.mp hAP
        have hx_mem : x ∈ A := singleton_subset_iff.mp hxA
        refine mem_powersetCard.mpr ⟨?_, by rw [card_erase_of_mem hx_mem, hA_card]⟩
        intro y hy
        obtain ⟨hy_ne, hyA⟩ := mem_erase.mp hy
        exact mem_erase.mpr ⟨hy_ne, hA_sub hyA⟩
      calc F.card = (F.image (fun A => A.erase x)).card := (card_image_of_injOn hinj).symm
        _ ≤ ((P.erase x).powersetCard (m - 1)).card := card_le_card himg
        _ = (P.card - 1).choose (m - 1) := by rw [card_powersetCard, card_erase_of_mem hxP]
    exact (sum_le_sum hfib).trans_eq (by rw [sum_const, smul_eq_mul])
  have hchoose_id : P.card * (P.card - 1).choose (m - 1) = P.card.choose m * m := by
    have hP_eq : P.card - 1 + 1 = P.card := by omega
    have hm_eq : m - 1 + 1 = m := by omega
    have h := Nat.add_one_mul_choose_eq (P.card - 1) (m - 1)
    rwa [hP_eq, hm_eq] at h
  have h2bad : P.card * (2 * badF.card) ≤ P.card * (P.powersetCard m).card := by
    rw [card_powersetCard]
    calc P.card * (2 * badF.card)
        = 2 * (P.card * badF.card) := by ring
      _ ≤ 2 * (P.card * ((P \ R).card * (P.card - 1).choose (m - 1))) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left P.card hbad_card)
      _ = 2 * (P \ R).card * (P.card * (P.card - 1).choose (m - 1)) := by ring
      _ = (2 * (P \ R).card * m) * P.card.choose m := by rw [hchoose_id]; ring
      _ ≤ P.card * P.card.choose m := Nat.mul_le_mul_right _ hbad
  have h2bad_le : 2 * badF.card ≤ (P.powersetCard m).card :=
    Nat.le_of_mul_le_mul_left h2bad hP_pos
  omega

private lemma rate_le_of_slope_le' {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) {E : ℝ}
    (hE : 0 ≤ E) (h : stencilSlope c ≤ (m : ℝ) * (1 - 1 / (B : ℝ) + E)) :
    rate c m B ≤ 2 * E := by
  have hm := hP.m_pos
  have hd := hP.one_sub_pos
  have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast hP.two_le_B
  have hd2 : 1 / 2 ≤ 1 - 1 / (B : ℝ) := by
    have : 1 / (B : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hB2
    linarith
  have hE2 : E ≤ 2 * E * (1 - 1 / (B : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * (1 - 1 / (B : ℝ)) by linarith) hE
    linarith
  rw [rate, normSlope, sub_le_iff_le_add, div_le_iff₀ (mul_pos hm hd)]
  calc stencilSlope c ≤ (m : ℝ) * (1 - 1 / (B : ℝ) + E) := h
    _ ≤ (m : ℝ) * (1 - 1 / (B : ℝ) + 2 * E * (1 - 1 / (B : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) hm.le
    _ = (2 * E + 1) * ((m : ℝ) * (1 - 1 / (B : ℝ))) := by ring

private lemma hammingCluster_pay_of_not_aligned {b : ℕ → ℤ} {N K W S M₀ B₀ r : ℕ} {x : ℕ × ℕ}
    (hK_pos : 0 < K) (hB₀_pos : 0 < B₀)
    (hC_pos_nat : 0 < (clusterPrimes W S x.1).card)
    (hLK_all : ∀ p₁ ∈ clusterPrimes W S x.1, ∀ p₂ ∈ clusterPrimes W S x.1,
      2 ≤ hammingLetter K W S (x.1 ^ x.2) p₁ p₂ ∧ hammingLetter K W S (x.1 ^ x.2) p₁ p₂ ≤ K)
    (hnot : (clusterPrimes W S x.1).card ^ 2 ≤
      16 * M₀ * (((clusterPrimes W S x.1) ×ˢ (clusterPrimes W S x.1)).filter
        fun p => B₀ ≤ r % hammingLetter K W S (x.1 ^ x.2) p.1 p.2).card) :
    (tautDefect b N (x.1 ^ x.2) : ℝ) ≤
      ((16 * (M₀ : ℝ) * (K : ℝ) / (B₀ : ℝ)) * (tautDefect b N (x.1 ^ x.2) : ℝ)) *
        ((1 / ((clusterPrimes W S x.1).card ^ 2 : ℝ)) *
          ∑ p ∈ clusterPrimes W S x.1 ×ˢ clusterPrimes W S x.1,
            ((r % hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℕ) : ℝ) /
              (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ)) := by
  have hKR_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
  have hBR_pos : (0 : ℝ) < (B₀ : ℝ) := by exact_mod_cast hB₀_pos
  set C_x := clusterPrimes W S x.1
  set badP := (C_x ×ˢ C_x).filter
    fun p => B₀ ≤ r % hammingLetter K W S (x.1 ^ x.2) p.1 p.2
  have hC_pos : (0 : ℝ) < (C_x.card : ℝ) := by exact_mod_cast hC_pos_nat
  have hsum_bad : (badP.card : ℝ) * ((B₀ : ℝ) / (K : ℝ)) ≤
      ∑ p ∈ C_x ×ˢ C_x,
        ((r % hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℕ) : ℝ) /
          (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) := by
    have hsub : badP ⊆ C_x ×ˢ C_x := filter_subset _ _
    refine le_trans ?_
      (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity)
    have hterm_ge : ∀ p ∈ badP,
        (B₀ : ℝ) / (K : ℝ) ≤
          ((r % hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℕ) : ℝ) /
            (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) := by
      intro p hp
      obtain ⟨hp_mem, hp_ge⟩ := mem_filter.mp hp
      obtain ⟨hp₁, hp₂⟩ := mem_product.mp hp_mem
      obtain ⟨hL2, hLK⟩ := hLK_all p.1 hp₁ p.2 hp₂
      have hLR_pos : (0 : ℝ) < (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) := by
        exact_mod_cast (by omega : 0 < hammingLetter K W S (x.1 ^ x.2) p.1 p.2)
      calc (B₀ : ℝ) / (K : ℝ)
          ≤ (B₀ : ℝ) / (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) :=
            div_le_div_of_nonneg_left hBR_pos.le hLR_pos (by exact_mod_cast hLK)
        _ ≤ ((r % hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℕ) : ℝ) /
              (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) :=
            div_le_div_of_nonneg_right (by exact_mod_cast hp_ge) hLR_pos.le
    exact (le_of_eq (by rw [sum_const, nsmul_eq_mul])).trans (sum_le_sum hterm_ge)
  have hcard_R : (C_x.card : ℝ) ^ 2 ≤ 16 * (M₀ : ℝ) * (badP.card : ℝ) := by exact_mod_cast hnot
  set S_val := ∑ p ∈ C_x ×ˢ C_x,
    ((r % hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℕ) : ℝ) /
      (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ)
  have h1 : (C_x.card : ℝ) ^ 2 * ((B₀ : ℝ) / (K : ℝ)) ≤ 16 * (M₀ : ℝ) * S_val := by
    calc (C_x.card : ℝ) ^ 2 * ((B₀ : ℝ) / (K : ℝ))
        ≤ (16 * (M₀ : ℝ) * (badP.card : ℝ)) * ((B₀ : ℝ) / (K : ℝ)) :=
          mul_le_mul_of_nonneg_right hcard_R (by positivity)
      _ = 16 * (M₀ : ℝ) * ((badP.card : ℝ) * ((B₀ : ℝ) / (K : ℝ))) := by ring
      _ ≤ 16 * (M₀ : ℝ) * S_val := mul_le_mul_of_nonneg_left hsum_bad (by positivity)
  have hratio : 1 ≤ (16 * (M₀ : ℝ) * (K : ℝ) / (B₀ : ℝ)) *
      ((1 / ((C_x.card : ℝ) ^ 2)) * S_val) := by
    have hpos_den : 0 < (C_x.card : ℝ) ^ 2 * (B₀ : ℝ) := by positivity
    have hmul : (C_x.card : ℝ) ^ 2 * (B₀ : ℝ) ≤ 16 * (M₀ : ℝ) * (K : ℝ) * S_val := by
      have := mul_le_mul_of_nonneg_right h1 hKR_pos.le
      have e : (C_x.card : ℝ) ^ 2 * ((B₀ : ℝ) / (K : ℝ)) * (K : ℝ) =
          (C_x.card : ℝ) ^ 2 * (B₀ : ℝ) := by field_simp [hKR_pos.ne']
      linarith
    have hdiv1 := (one_le_div hpos_den).mpr hmul
    refine hdiv1.trans_eq ?_
    field_simp [hBR_pos.ne', hC_pos.ne']
  calc (tautDefect b N (x.1 ^ x.2) : ℝ)
      = 1 * (tautDefect b N (x.1 ^ x.2) : ℝ) := (one_mul _).symm
    _ ≤ ((16 * (M₀ : ℝ) * (K : ℝ) / (B₀ : ℝ)) * ((1 / ((C_x.card : ℝ) ^ 2)) * S_val)) *
          (tautDefect b N (x.1 ^ x.2) : ℝ) :=
        mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg _)
    _ = _ := by ring

private lemma hammingCluster_slope_le {b : ℕ → ℤ} {N P_max K W S M₀ B₀ : ℕ}
    (hK1 : 1 ≤ K) (hB₀_pos : 0 < B₀)
    (hC_pos_all : ∀ x : ℕ × ℕ, 0 < (clusterPrimes W S x.1).card)
    (hcl_bounds : ∀ x ∈ oddPrimePowers P_max,
      ∀ p₁ ∈ clusterPrimes W S x.1, ∀ p₂ ∈ clusterPrimes W S x.1,
        2 ≤ hammingLetter K W S (x.1 ^ x.2) p₁ p₂ ∧
        hammingLetter K W S (x.1 ^ x.2) p₁ p₂ ≤ K ∧
        K < 2 ^ (2 * S + 1) * hammingLetter K W S (x.1 ^ x.2) p₁ p₂) :
    ∑ x ∈ oddPrimePowers P_max,
      ((16 * (M₀ : ℝ) * (K : ℝ) / (B₀ : ℝ)) * (tautDefect b N (x.1 ^ x.2) : ℝ)) *
        ((1 / ((clusterPrimes W S x.1).card ^ 2 : ℝ)) *
          ∑ p ∈ clusterPrimes W S x.1 ×ˢ clusterPrimes W S x.1,
            Real.log (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) /
              (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ)) ≤
      (16 * (M₀ : ℝ) * (2 ^ (2 * S + 1) : ℝ) * Real.log (K : ℝ) / (B₀ : ℝ)) *
        ((Nat.log 2 N : ℝ) + 1) ^ 2 * tautMass b N := by
  have hKR_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hBR_pos : (0 : ℝ) < (B₀ : ℝ) := by exact_mod_cast hB₀_pos
  have hlogK_nn : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK1)
  have hper_x : ∀ x ∈ oddPrimePowers P_max,
      ((16 * (M₀ : ℝ) * (K : ℝ) / (B₀ : ℝ)) * (tautDefect b N (x.1 ^ x.2) : ℝ)) *
        ((1 / ((clusterPrimes W S x.1).card ^ 2 : ℝ)) *
          ∑ p ∈ clusterPrimes W S x.1 ×ˢ clusterPrimes W S x.1,
            Real.log (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) /
              (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ)) ≤
      (16 * (M₀ : ℝ) * (2 ^ (2 * S + 1) : ℝ) * Real.log (K : ℝ) / (B₀ : ℝ)) *
        (tautDefect b N (x.1 ^ x.2) : ℝ) := by
    intro x hx
    set C_x := clusterPrimes W S x.1
    have hC_ne : (C_x.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hC_pos_all x).ne'
    have hp_bd : ∀ p ∈ C_x ×ˢ C_x,
        Real.log (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) /
          (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) ≤
        Real.log (K : ℝ) * ((2 ^ (2 * S + 1) : ℝ) / (K : ℝ)) := by
      intro p hp
      obtain ⟨hp₁, hp₂⟩ := mem_product.mp hp
      obtain ⟨hL2, hLK, hKL⟩ := hcl_bounds x hx p.1 hp₁ p.2 hp₂
      have hLR_pos : (0 : ℝ) < (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) := by
        exact_mod_cast (by omega : 0 < hammingLetter K W S (x.1 ^ x.2) p.1 p.2)
      have hlog_le : Real.log (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) ≤ Real.log (K : ℝ) :=
        Real.log_le_log hLR_pos (by exact_mod_cast hLK)
      have hinv_le : 1 / (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) ≤
          (2 ^ (2 * S + 1) : ℝ) / (K : ℝ) := by
        rw [div_le_div_iff₀ hLR_pos hKR_pos, one_mul]
        exact_mod_cast hKL.le
      calc Real.log (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) /
            (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ)
          = Real.log (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) *
              (1 / (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ)) := by ring
        _ ≤ Real.log (K : ℝ) * ((2 ^ (2 * S + 1) : ℝ) / (K : ℝ)) :=
            mul_le_mul hlog_le hinv_le (by positivity) hlogK_nn
    have hsum_p : (1 / ((C_x.card : ℝ) ^ 2)) *
        (∑ p ∈ C_x ×ˢ C_x,
          Real.log (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) /
            (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ)) ≤
        Real.log (K : ℝ) * ((2 ^ (2 * S + 1) : ℝ) / (K : ℝ)) := by
      have hs : ∑ p ∈ C_x ×ˢ C_x,
          Real.log (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) /
            (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) ≤
          (C_x.card : ℝ) ^ 2 * (Real.log (K : ℝ) * ((2 ^ (2 * S + 1) : ℝ) / (K : ℝ))) :=
        (sum_le_sum hp_bd).trans_eq
          (by rw [sum_const, card_product, nsmul_eq_mul]; push_cast; ring)
      calc (1 / ((C_x.card : ℝ) ^ 2)) * _
          ≤ (1 / ((C_x.card : ℝ) ^ 2)) *
              ((C_x.card : ℝ) ^ 2 * (Real.log (K : ℝ) * ((2 ^ (2 * S + 1) : ℝ) / (K : ℝ)))) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = Real.log (K : ℝ) * ((2 ^ (2 * S + 1) : ℝ) / (K : ℝ)) := by
            field_simp [hC_ne]
    calc _ ≤ ((16 * (M₀ : ℝ) * (K : ℝ) / (B₀ : ℝ)) * (tautDefect b N (x.1 ^ x.2) : ℝ)) *
            (Real.log (K : ℝ) * ((2 ^ (2 * S + 1) : ℝ) / (K : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum_p (by positivity)
      _ = (16 * (M₀ : ℝ) * (2 ^ (2 * S + 1) : ℝ) * Real.log (K : ℝ) / (B₀ : ℝ)) *
            (tautDefect b N (x.1 ^ x.2) : ℝ) := by
          field_simp [hKR_pos.ne', hBR_pos.ne']
  refine (sum_le_sum hper_x).trans ?_
  rw [← mul_sum]
  calc (16 * (M₀ : ℝ) * (2 ^ (2 * S + 1) : ℝ) * Real.log (K : ℝ) / (B₀ : ℝ)) *
        (∑ x ∈ oddPrimePowers P_max, (tautDefect b N (x.1 ^ x.2) : ℝ))
      ≤ (16 * (M₀ : ℝ) * (2 ^ (2 * S + 1) : ℝ) * Real.log (K : ℝ) / (B₀ : ℝ)) *
          (((Nat.log 2 N : ℝ) + 1) ^ 2 * tautMass b N) :=
        mul_le_mul_of_nonneg_left (sum_tautDefect_le b N P_max) (by positivity)
    _ = _ := by ring

private def hammingClusterTerm (b : ℕ → ℤ) (N K W S M₀ B₀ : ℕ) (x : ℕ × ℕ) (r : ℕ) : ℝ :=
  ((16 * (M₀ : ℝ) * (K : ℝ) / (B₀ : ℝ)) * (tautDefect b N (x.1 ^ x.2) : ℝ)) *
    ((1 / ((clusterPrimes W S x.1).card ^ 2 : ℝ)) *
      ∑ p ∈ clusterPrimes W S x.1 ×ˢ clusterPrimes W S x.1,
        ((r % hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℕ) : ℝ) /
          (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ))

private lemma hammingClusterTerm_nonneg (b : ℕ → ℤ) (N K W S M₀ B₀ : ℕ) (x : ℕ × ℕ) (r : ℕ) :
    0 ≤ hammingClusterTerm b N K W S M₀ B₀ x r := by
  unfold hammingClusterTerm
  refine mul_nonneg (by positivity) (mul_nonneg (by positivity) (sum_nonneg fun _ _ => ?_))
  positivity

private def hammingRampTerm (Y_rat : ℚ) (I_ramp : Finset (Finset ℕ)) (r : ℕ) : ℝ :=
  (4 * (Y_rat : ℝ) / (I_ramp.card : ℝ)) * ∑ A ∈ I_ramp, ((r % A.prod id : ℕ) : ℝ)

private lemma hammingRampTerm_nonneg {Y_rat : ℚ} (hY : 0 ≤ (Y_rat : ℝ))
    (I_ramp : Finset (Finset ℕ)) (r : ℕ) :
    0 ≤ hammingRampTerm Y_rat I_ramp r := by
  unfold hammingRampTerm
  exact mul_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg _))
    (sum_nonneg fun _ _ => Nat.cast_nonneg _)

private lemma hammingTotal_win_ge_one {b : ℕ → ℤ} {N K W S M₀ B₀ X : ℕ} {Y_n : ℝ} {Y_rat : ℚ}
    {Q_set : Finset (ℕ × ℕ)} {I_ramp : Finset (Finset ℕ)}
    (hYrat_nn : 0 ≤ (Y_rat : ℝ)) (hYrat_ge : Y_n ≤ (Y_rat : ℝ))
    (hIramp_pos : 0 < I_ramp.card)
    (hramp_bounds : ∀ A ∈ I_ramp, B₀ < A.prod id ∧ A.prod id ≤ K)
    (hB₀_le_X : B₀ ≤ X)
    (hnear_X : ∀ s : ℕ, 1 ≤ s → s ≤ X → |tautNear b N s - 1| ≤ (s : ℝ) * Y_n)
    {r : ℕ} (hr1 : 1 ≤ r) (hrB : r < B₀) :
    1 ≤ tautNear b N r + (∑ x ∈ Q_set, hammingClusterTerm b N K W S M₀ B₀ x r) +
      hammingRampTerm Y_rat I_ramp r := by
  have hnear_r := (abs_le.mp (hnear_X r hr1 (hrB.le.trans hB₀_le_X))).1
  have hramp_eq : hammingRampTerm Y_rat I_ramp r = 4 * (Y_rat : ℝ) * (r : ℝ) := by
    unfold hammingRampTerm
    have hmod_eq : ∀ A ∈ I_ramp, ((r % A.prod id : ℕ) : ℝ) = (r : ℝ) :=
      fun A hA => by rw [Nat.mod_eq_of_lt (hrB.trans (hramp_bounds A hA).1)]
    rw [sum_congr rfl hmod_eq, sum_const, nsmul_eq_mul]
    have hcard_ne : (I_ramp.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hIramp_pos.ne'
    field_simp [hcard_ne]
  have hcl_nn : 0 ≤ ∑ x ∈ Q_set, hammingClusterTerm b N K W S M₀ B₀ x r :=
    sum_nonneg fun x _ => hammingClusterTerm_nonneg b N K W S M₀ B₀ x r
  have hr_nn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hY_cmp : (r : ℝ) * Y_n ≤ 4 * (Y_rat : ℝ) * (r : ℝ) := by
    nlinarith only [hYrat_nn, hYrat_ge, hr_nn]
  linarith only [hnear_r, hramp_eq, hcl_nn, hY_cmp]

private lemma hammingTotal_nonneg {b : ℕ → ℤ} {N P_max M₀ W K S B₀ X m_star : ℕ}
    {Y_n : ℝ} {Y_rat : ℚ}
    {P_set : Finset ℕ} {Q_set : Finset (ℕ × ℕ)} {I_ramp : Finset (Finset ℕ)}
    (hN2 : 2 ≤ N) (hb2 : b 2 = -1)
    (hb_smooth : ∀ k : ℕ, 2 ≤ k → k ≤ N → b k ≠ 0 → ¬ 4 ∣ k ∧
      ∀ q e : ℕ, q.Prime → 1 ≤ e → q ^ e ∣ k → q ^ e ≤ P_max)
    (hM₀ : 2 ≤ M₀) (hW : 2 ≤ W) (hK_pos : 0 < K) (hB₀_pos : 0 < B₀)
    (hS_def : S = 16 * M₀ + 4)
    (hK_sq : 2 ^ (2 * S + 2) * W ^ 2 * (P_max + 1) ≤ K)
    (hm_lo : 1 ≤ m_star) (hm_hi : m_star < M₀)
    (hP_def : P_set = bertrandPrimes W S) (hP_card_ge : S ≤ P_set.card) (hm_le_P : m_star ≤ P_set.card)
    (hQ_def : Q_set = oddPrimePowers P_max)
    (hIramp_def : I_ramp = P_set.powersetCard m_star) (hIramp_pos : 0 < I_ramp.card)
    (hC_card_pos : ∀ x : ℕ × ℕ, 0 < (clusterPrimes W S x.1).card)
    (hramp_bounds : ∀ A ∈ I_ramp, B₀ < A.prod id ∧ A.prod id ≤ K)
    (hcl_bounds : ∀ x ∈ Q_set, ∀ p₁ ∈ clusterPrimes W S x.1, ∀ p₂ ∈ clusterPrimes W S x.1,
      2 ≤ hammingLetter K W S (x.1 ^ x.2) p₁ p₂ ∧
      hammingLetter K W S (x.1 ^ x.2) p₁ p₂ ≤ K ∧
      K < 2 ^ (2 * S + 1) * hammingLetter K W S (x.1 ^ x.2) p₁ p₂ ∧
      B₀ < hammingBase K W S (x.1 ^ x.2) p₁)
    (hYn_nn : 0 ≤ Y_n) (hYrat_nn : 0 ≤ (Y_rat : ℝ)) (hYrat_ge : Y_n ≤ (Y_rat : ℝ))
    (hB₀_le_X : B₀ ≤ X)
    (hnear_X : ∀ s : ℕ, 1 ≤ s → s ≤ X → |tautNear b N s - 1| ≤ (s : ℝ) * Y_n)
    (r : ℕ) :
    0 ≤ tautNear b N r + (∑ x ∈ Q_set, hammingClusterTerm b N K W S M₀ B₀ x r) +
      hammingRampTerm Y_rat I_ramp r := by
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [tautNear_zero]
    linarith only [sum_nonneg (fun x (_ : x ∈ Q_set) => hammingClusterTerm_nonneg b N K W S M₀ B₀ x 0),
      hammingRampTerm_nonneg hYrat_nn I_ramp 0]
  by_cases hrB : r < B₀
  · exact zero_le_one.trans (hammingTotal_win_ge_one hYrat_nn hYrat_ge hIramp_pos hramp_bounds
      hB₀_le_X hnear_X (by omega) hrB)
  push Not at hrB
  let isAligned : ℕ × ℕ → Prop := fun x =>
    16 * M₀ * (((clusterPrimes W S x.1) ×ˢ (clusterPrimes W S x.1)).filter
      fun p => B₀ ≤ r % hammingLetter K W S (x.1 ^ x.2) p.1 p.2).card <
    (clusterPrimes W S x.1).card ^ 2
  have hunaligned_pay : ∀ x ∈ Q_set, ¬ isAligned x →
      (tautDefect b N (x.1 ^ x.2) : ℝ) ≤ hammingClusterTerm b N K W S M₀ B₀ x r := by
    intro x hx hnot
    dsimp [isAligned] at hnot
    push Not at hnot
    unfold hammingClusterTerm
    exact hammingCluster_pay_of_not_aligned hK_pos hB₀_pos (hC_card_pos x)
      (fun p₁ hp₁ p₂ hp₂ => ⟨(hcl_bounds x hx p₁ hp₁ p₂ hp₂).1,
        (hcl_bounds x hx p₁ hp₁ p₂ hp₂).2.1⟩) hnot
  by_cases hex_al : ∃ x ∈ Q_set, isAligned x
  · obtain ⟨x₀, hx₀, hal₀⟩ := hex_al
    have hx₀_mem : x₀ ∈ oddPrimePowers P_max := hQ_def ▸ hx₀
    obtain ⟨_, hqp₀, _, hQP₀⟩ := mem_oddPrimePowers_iff.mp hx₀_mem
    have hC₀_eq : P_set.erase x₀.1 = clusterPrimes W S x₀.1 := by rw [hP_def]; rfl
    have hspec₀ := alignedRows_spec (P := P_set) (q := x₀.1) (K := K) (W := W) (S := S)
      (Q := x₀.1 ^ x₀.2) (B₀ := B₀) (r := r) (M₀ := M₀) hM₀
      (hC₀_eq ▸ hC_card_pos x₀)
      (fun p hp => (hcl_bounds x₀ hx₀ p (hC₀_eq ▸ hp) p (hC₀_eq ▸ hp)).2.2.2)
      (hammingExp_pos hW (pow_pos hqp₀.pos _) hQP₀ hK_sq)
      (by simpa only [hC₀_eq] using hal₀)
    obtain ⟨hR₀_sub, hR₀_sdiff, h, hh_lt, h2_dvd, _, hp₀_dvd⟩ := hspec₀
    set R₀ := alignedRows K W S (x₀.1 ^ x₀.2) B₀ r (P_set.erase x₀.1)
    have hh_le_r : h ≤ r := hh_lt.le.trans hrB
    have hall_al_dvd : ∀ x ∈ Q_set, isAligned x → x.1 ^ x.2 ∣ r - h := by
      intro x hx halx
      have hx_mem : x ∈ oddPrimePowers P_max := hQ_def ▸ hx
      obtain ⟨_, hqpx, _, hQPx⟩ := mem_oddPrimePowers_iff.mp hx_mem
      have hCx_eq : P_set.erase x.1 = clusterPrimes W S x.1 := by rw [hP_def]; rfl
      obtain ⟨hRx_sub, hRx_sdiff, hx_val, hhx_lt, _, hQx_dvd, hpx_dvd⟩ :=
        alignedRows_spec (P := P_set) (q := x.1) (K := K) (W := W) (S := S)
          (Q := x.1 ^ x.2) (B₀ := B₀) (r := r) (M₀ := M₀) hM₀
          (hCx_eq ▸ hC_card_pos x)
          (fun p hp => (hcl_bounds x hx p (hCx_eq ▸ hp) p (hCx_eq ▸ hp)).2.2.2)
          (hammingExp_pos hW (pow_pos hqpx.pos _) hQPx hK_sq)
          (by simpa only [hCx_eq] using halx)
      set Rx := alignedRows K W S (x.1 ^ x.2) B₀ r (P_set.erase x.1)
      have hsdiff_inter : P_set \ (R₀ ∩ Rx) ⊆ (P_set \ R₀) ∪ (P_set \ Rx) := by
        intro p hp
        obtain ⟨hpP, hpI⟩ := mem_sdiff.mp hp
        by_cases hp0 : p ∈ R₀
        · exact mem_union_right _ (mem_sdiff.mpr ⟨hpP, fun hpx => hpI (mem_inter.mpr ⟨hp0, hpx⟩)⟩)
        · exact mem_union_left _ (mem_sdiff.mpr ⟨hpP, hp0⟩)
      have hsdiff_le : (P_set \ (R₀ ∩ Rx)).card ≤ (P_set \ R₀).card + (P_set \ Rx).card :=
        (card_le_card hsdiff_inter).trans (card_union_le _ _)
      have hinter_part : (P_set \ (R₀ ∩ Rx)).card + (R₀ ∩ Rx).card = P_set.card :=
        card_sdiff_add_card_eq_card (inter_subset_left.trans hR₀_sub)
      have hm_le_inter : m_star ≤ (R₀ ∩ Rx).card := by
        have h8D : 8 * M₀ * (P_set \ (R₀ ∩ Rx)).card ≤ 2 * P_set.card + 16 * M₀ := by
          have hmul := Nat.mul_le_mul_left (8 * M₀) hsdiff_le
          rw [mul_add] at hmul
          omega
        have hlin : 8 * (M₀ * P_set.card) =
            8 * M₀ * (P_set \ (R₀ ∩ Rx)).card + 8 * M₀ * (R₀ ∩ Rx).card := by
          calc 8 * (M₀ * P_set.card)
              = 8 * M₀ * P_set.card := (mul_assoc 8 M₀ P_set.card).symm
            _ = 8 * M₀ * ((P_set \ (R₀ ∩ Rx)).card + (R₀ ∩ Rx).card) := by rw [hinter_part]
            _ = _ := mul_add _ _ _
        have h2P : 2 * P_set.card ≤ M₀ * P_set.card := Nat.mul_le_mul_right P_set.card hM₀
        have hMP : 16 * (M₀ * M₀) + 4 * M₀ ≤ M₀ * P_set.card := by
          calc 16 * (M₀ * M₀) + 4 * M₀ = M₀ * (16 * M₀ + 4) := by ring
            _ ≤ M₀ * P_set.card := Nat.mul_le_mul_left M₀ (hS_def ▸ hP_card_ge)
        have hM_inter : 8 * (M₀ * M₀) ≤ 8 * M₀ * (R₀ ∩ Rx).card := by omega
        have hM_inter' : 8 * M₀ * M₀ ≤ 8 * M₀ * (R₀ ∩ Rx).card := by
          rwa [← mul_assoc 8 M₀ M₀] at hM_inter
        have : M₀ ≤ (R₀ ∩ Rx).card :=
          Nat.le_of_mul_le_mul_left hM_inter' (by positivity)
        omega
      obtain ⟨A, hA_sub_I, hA_card⟩ := exists_subset_card_eq hm_le_inter
      have hA_mem : A ∈ I_ramp := by
        rw [hIramp_def, mem_powersetCard]
        exact ⟨hA_sub_I.trans (inter_subset_left.trans hR₀_sub), hA_card⟩
      have hB₀_lt_MA := (hramp_bounds A hA_mem).1
      have hprimes_A : ∀ p ∈ A, Prime p := fun p hp => by
        have hp_b : p ∈ bertrandPrimes W S :=
          hP_def ▸ (hA_sub_I.trans (inter_subset_left.trans hR₀_sub)) hp
        exact (mem_bertrandPrimes.mp hp_b).2.prime
      have hdvd_0 : A.prod id ∣ r - h := Finset.prod_primes_dvd (r - h) hprimes_A
        fun p hp => hp₀_dvd p ((mem_inter.mp (hA_sub_I hp)).1)
      have hdvd_x : A.prod id ∣ r - hx_val := Finset.prod_primes_dvd (r - hx_val) hprimes_A
        fun p hp => hpx_dvd p ((mem_inter.mp (hA_sub_I hp)).2)
      have hmod_0 : h = r % A.prod id := by
        have hm := (Nat.modEq_iff_dvd' hh_le_r).mpr hdvd_0
        rwa [Nat.ModEq, Nat.mod_eq_of_lt (hh_lt.trans hB₀_lt_MA)] at hm
      have hmod_x : hx_val = r % A.prod id := by
        have hm := (Nat.modEq_iff_dvd' (hhx_lt.le.trans hrB)).mpr hdvd_x
        rwa [Nat.ModEq, Nat.mod_eq_of_lt (hhx_lt.trans hB₀_lt_MA)] at hm
      have heq_h : hx_val = h := hmod_x.trans hmod_0.symm
      rwa [heq_h] at hQx_dvd
    have hnear_diff : |tautNear b N r - tautNear b N h| ≤
        ∑ x ∈ Q_set, hammingClusterTerm b N K W S M₀ B₀ x r := by
      have hd := abs_tautNear_sub_le_tautDefect (P_max := P_max) hb_smooth hh_le_r h2_dvd
      rw [← hQ_def] at hd
      refine hd.trans (sum_le_sum fun x hx => ?_)
      split_ifs with hdvd
      · exact hammingClusterTerm_nonneg b N K W S M₀ B₀ x r
      · exact hunaligned_pay x hx fun hal => hdvd (hall_al_dvd x hx hal)
    rcases eq_or_ne h 0 with rfl | hh0
    · rw [tautNear_zero, sub_zero] at hnear_diff
      linarith only [(abs_le.mp hnear_diff).1, hammingRampTerm_nonneg hYrat_nn I_ramp r]
    · have hbad_half : 2 * (P_set \ R₀).card * m_star ≤ P_set.card := by
        have h4M : 4 * M₀ * (2 * (P_set \ R₀).card * m_star) ≤ 4 * M₀ * P_set.card := by
          have h1 : (8 * M₀ * (P_set \ R₀).card) * m_star ≤ (P_set.card + 8 * M₀) * M₀ :=
            Nat.mul_le_mul (by omega) (by omega)
          have hMP : M₀ * (16 * M₀ + 4) ≤ M₀ * P_set.card :=
            Nat.mul_le_mul_left M₀ (hS_def ▸ hP_card_ge)
          have h8_le : 8 * (M₀ * M₀) ≤ 3 * (M₀ * (16 * M₀ + 4)) := by
            calc 8 * (M₀ * M₀) ≤ 48 * (M₀ * M₀) + 12 * M₀ := by omega
              _ = 3 * (M₀ * (16 * M₀ + 4)) := by ring
          calc 4 * M₀ * (2 * (P_set \ R₀).card * m_star)
              = (8 * M₀ * (P_set \ R₀).card) * m_star := by ring
            _ ≤ (P_set.card + 8 * M₀) * M₀ := h1
            _ = M₀ * P_set.card + 8 * (M₀ * M₀) := by ring
            _ ≤ M₀ * P_set.card + 3 * (M₀ * (16 * M₀ + 4)) := Nat.add_le_add_left h8_le _
            _ ≤ M₀ * P_set.card + 3 * (M₀ * P_set.card) :=
                Nat.add_le_add_left (Nat.mul_le_mul_left 3 hMP) _
            _ = 4 * M₀ * P_set.card := by ring
        exact Nat.le_of_mul_le_mul_left h4M (by positivity)
      have hhalf := powersetCard_half_subset hm_lo hm_le_P hbad_half
      set goodRamp := I_ramp.filter (· ⊆ R₀)
      have hramp_ge : 2 * Y_n * (h : ℝ) ≤ hammingRampTerm Y_rat I_ramp r := by
        unfold hammingRampTerm
        have hsub_g : goodRamp ⊆ I_ramp := filter_subset _ _
        have hsub_sum : ∑ A ∈ goodRamp, ((r % A.prod id : ℕ) : ℝ) ≤
            ∑ A ∈ I_ramp, ((r % A.prod id : ℕ) : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub_g fun _ _ _ => Nat.cast_nonneg _
        have hgood_eq : ∀ A ∈ goodRamp, ((r % A.prod id : ℕ) : ℝ) = (h : ℝ) := by
          intro A hA
          obtain ⟨hAI, hAR⟩ := mem_filter.mp hA
          have hprimes_A : ∀ p ∈ A, Prime p := fun p hp => by
            have hp_b : p ∈ bertrandPrimes W S := hP_def ▸ (hR₀_sub (hAR hp))
            exact (mem_bertrandPrimes.mp hp_b).2.prime
          have hdvd_h : A.prod id ∣ r - h := Finset.prod_primes_dvd (r - h) hprimes_A
            fun p hp => hp₀_dvd p (hAR hp)
          have hm := (Nat.modEq_iff_dvd' hh_le_r).mpr hdvd_h
          rw [Nat.ModEq, Nat.mod_eq_of_lt (hh_lt.trans (hramp_bounds A hAI).1)] at hm
          rw [← hm]
        rw [sum_congr rfl hgood_eq, sum_const, nsmul_eq_mul] at hsub_sum
        have hhalf_R : (I_ramp.card : ℝ) ≤ 2 * (goodRamp.card : ℝ) := by
          dsimp [goodRamp]; rw [hIramp_def]; exact_mod_cast hhalf
        have hcard_pos : (0 : ℝ) < (I_ramp.card : ℝ) := by exact_mod_cast hIramp_pos
        have hfrac : (1 / 2 : ℝ) ≤ (goodRamp.card : ℝ) / (I_ramp.card : ℝ) := by
          rw [div_le_div_iff₀ (by norm_num) hcard_pos]; linarith only [hhalf_R]
        calc 2 * Y_n * (h : ℝ)
            ≤ 4 * (Y_rat : ℝ) * (1 / 2) * (h : ℝ) := by
              have hh_nn : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
              nlinarith only [hYrat_nn, hYrat_ge, hh_nn]
          _ ≤ 4 * (Y_rat : ℝ) * ((goodRamp.card : ℝ) / (I_ramp.card : ℝ)) * (h : ℝ) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hfrac (by linarith only [hYrat_nn])) (Nat.cast_nonneg h)
          _ = (4 * (Y_rat : ℝ) / (I_ramp.card : ℝ)) * ((goodRamp.card : ℝ) * (h : ℝ)) := by ring
          _ ≤ (4 * (Y_rat : ℝ) / (I_ramp.card : ℝ)) *
                ∑ A ∈ I_ramp, ((r % A.prod id : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hsub_sum (by positivity)
      have hnear_h := (abs_le.mp (hnear_X h (by omega) (hh_lt.le.trans hB₀_le_X))).1
      have hdiff_lo := (abs_le.mp hnear_diff).1
      have hprod_nn : 0 ≤ (h : ℝ) * Y_n := mul_nonneg (Nat.cast_nonneg h) hYn_nn
      have hprod_eq : 2 * Y_n * (h : ℝ) = 2 * ((h : ℝ) * Y_n) := by ring
      linarith only [hnear_h, hdiff_lo, hramp_ge, hprod_nn, hprod_eq]
  · push Not at hex_al
    have hsum_pay : ∑ x ∈ Q_set, (tautDefect b N (x.1 ^ x.2) : ℝ) ≤
        ∑ x ∈ Q_set, hammingClusterTerm b N K W S M₀ B₀ x r :=
      sum_le_sum fun x hx => hunaligned_pay x hx (hex_al x hx)
    have hneg_near := neg_sum_tautDefect_le_tautNear hN2 hb2 hb_smooth r
    rw [← hQ_def] at hneg_near
    linarith only [hsum_pay, hneg_near, hammingRampTerm_nonneg hYrat_nn I_ramp r]

/-- **Bipartite Hamming-square and subset-product CRT producer assembly.**
Given a smooth `4`-free stencil `b` supported in `[1, N]` tracking `M(x)` within `η₀ x`,
clearing denominators of the combined near, Hamming-square cluster, and subset-product ramp
letters yields an admissible integer producer `(c, m, B₀)` on `[1, K]`. -/
theorem exists_hamming_compensated_producer
    {b : ℕ → ℤ} {N P_max M₀ W K X : ℕ} {η₀ : ℝ}
    (hN2 : 2 ≤ N) (hb1 : b 1 = 1) (hb2 : b 2 = -1)
    (hb_supp : ∀ k : ℕ, N < k → b k = 0)
    (hb_smooth : ∀ k : ℕ, 2 ≤ k → k ≤ N → b k ≠ 0 → ¬ 4 ∣ k ∧
      ∀ q e : ℕ, q.Prime → 1 ≤ e → q ^ e ∣ k → q ^ e ≤ P_max)
    (hη₀ : 0 ≤ η₀)
    (hB_mert : ∀ x : ℕ, 1 ≤ x → |(∑ k ∈ Icc 1 x, (b k : ℝ)) - mertens x| ≤ η₀ * (x : ℝ))
    (hM₀ : 2 ≤ M₀) (hW : 2 ≤ W)
    (hNK : N ≤ K) (hKX : K ≤ X)
    (hm_lo : 1 ≤ Nat.log (2 ^ (16 * M₀ + 4) * W) K)
    (hm_hi : Nat.log (2 ^ (16 * M₀ + 4) * W) K < M₀)
    (hB₀_ge2 : 2 ≤ K / (2 ^ ((16 * M₀ + 4) * (M₀ + 1) + 2) * W))
    (hK_sq : 2 ^ (2 * (16 * M₀ + 4) + 2) * W ^ 2 * (P_max + 1) ≤ K) :
    let S := 16 * M₀ + 4
    let B₀ := K / (2 ^ (S * (M₀ + 1) + 2) * W)
    let Y_n := 2 * η₀ * (1 + Real.log (X : ℝ)) + (1 + tautMass b N) / (X : ℝ)
    ∃ (c : ℕ →₀ ℤ) (m : ℕ),
      IsProducer c m B₀ ∧ AlphabetLE c K ∧
      rate c m B₀ ≤ 2 * (Y_n * (1 + Real.log (B₀ : ℝ)) + 8 * Y_n * Real.log (K : ℝ) +
        tautMass b N / (B₀ : ℝ) +
        (16 * (M₀ : ℝ) * (2 ^ (2 * S + 1) : ℝ) * Real.log (K : ℝ) / (B₀ : ℝ)) *
          ((Nat.log 2 N : ℝ) + 1) ^ 2 * tautMass b N) := by
  intro S B₀ Y_n
  have hS_def : S = 16 * M₀ + 4 := rfl
  have hB₀_def : B₀ = K / (2 ^ (S * (M₀ + 1) + 2) * W) := rfl
  have hB₀2 : 2 ≤ B₀ := hB₀_ge2
  have hB₀_pos : 0 < B₀ := by omega
  have hK_ge2 : 2 ≤ K := hN2.trans hNK
  have hK_pos : 0 < K := by omega
  have hX_ge2 : 2 ≤ X := hK_ge2.trans hKX
  have hKR_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
  have hBR_pos : (0 : ℝ) < (B₀ : ℝ) := by exact_mod_cast hB₀_pos
  have hYn_pos : 0 < Y_n := by
    dsimp [Y_n]
    have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
    have hmass0 := tautMass_nonneg b N
    positivity
  obtain ⟨Y_rat, hYrat_gt, hYrat_lt⟩ := exists_rat_btwn (lt_two_mul_self hYn_pos)
  have hYrat_ge : Y_n ≤ (Y_rat : ℝ) := hYrat_gt.le
  have hYrat_le : (Y_rat : ℝ) ≤ 2 * Y_n := hYrat_lt.le
  have hYrat_nn : 0 ≤ (Y_rat : ℝ) := hYn_pos.le.trans hYrat_ge
  -- Set up prime pool `P_set` and subset size `m_*`.
  obtain ⟨m_star, hm_def⟩ : ∃ m_star : ℕ, m_star = Nat.log (2 ^ S * W) K := ⟨_, rfl⟩
  rw [← hS_def, ← hm_def] at hm_lo hm_hi
  obtain ⟨P_set, hP_def⟩ : ∃ P_set : Finset ℕ, P_set = bertrandPrimes W S := ⟨_, rfl⟩
  have hP_card_ge : S ≤ P_set.card := by
    rw [hP_def]; exact le_card_bertrandPrimes (by omega) S
  have hm_le_P : m_star ≤ P_set.card := by omega
  obtain ⟨I_ramp, hIramp_def⟩ : ∃ I_ramp : Finset (Finset ℕ),
      I_ramp = P_set.powersetCard m_star := ⟨_, rfl⟩
  have hIramp_pos : 0 < I_ramp.card := by
    rw [hIramp_def, card_powersetCard]; exact Nat.choose_pos hm_le_P
  have hramp_bounds : ∀ A ∈ I_ramp, B₀ < A.prod id ∧ A.prod id ≤ K := by
    intro A hA
    rw [hIramp_def, mem_powersetCard] at hA
    obtain ⟨hA_sub, hA_card⟩ := hA
    refine ⟨?_, ?_⟩
    · have hbase_gt1 : 1 < 2 ^ S * W := by
        calc 1 < 2 := by norm_num
          _ ≤ 1 * W := by omega
          _ ≤ 2 ^ S * W := Nat.mul_le_mul_right W Nat.one_le_two_pow
      have hK_lt_pow : K < (2 ^ S * W) ^ (m_star + 1) := by
        rw [hm_def]; exact Nat.lt_pow_succ_log_self hbase_gt1 K
      have hpow_eq : (2 ^ S * W) ^ (m_star + 1) =
          (2 ^ (S * (m_star + 1)) * W) * W ^ m_star := by
        rw [mul_pow, ← pow_mul, pow_succ']; ring
      rw [hpow_eq] at hK_lt_pow
      have hdiv_lt : K / (2 ^ (S * (m_star + 1)) * W) < W ^ m_star :=
        Nat.div_lt_of_lt_mul hK_lt_pow
      have hexp_le : S * (m_star + 1) ≤ S * (M₀ + 1) + 2 := by
        have : m_star + 1 ≤ M₀ + 1 := by omega
        exact (Nat.mul_le_mul_left S this).trans (Nat.le_add_right _ 2)
      have hden_le : 2 ^ (S * (m_star + 1)) * W ≤ 2 ^ (S * (M₀ + 1) + 2) * W :=
        Nat.mul_le_mul_right W (Nat.pow_le_pow_right (by norm_num) hexp_le)
      have hB₀_lt_W : B₀ < W ^ m_star := by
        rw [hB₀_def]
        exact (Nat.div_le_div_left hden_le (by positivity)).trans_lt hdiv_lt
      have hW_le_prod : W ^ m_star ≤ A.prod id := by
        rw [← hA_card, ← Finset.prod_const]
        refine Finset.prod_le_prod (fun _ _ => Nat.zero_le W) fun p hp => ?_
        have hp_mem : p ∈ bertrandPrimes W S := hP_def ▸ hA_sub hp
        exact (mem_bertrandPrimes.mp hp_mem).1.1.le
      exact hB₀_lt_W.trans_le hW_le_prod
    · have hprod_le : A.prod id ≤ (2 ^ S * W) ^ m_star := by
        rw [← hA_card, ← Finset.prod_const]
        refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun p hp => ?_
        have hp_mem : p ∈ bertrandPrimes W S := hP_def ▸ hA_sub hp
        exact (mem_bertrandPrimes.mp hp_mem).1.2
      have hpow_le_K : (2 ^ S * W) ^ m_star ≤ K := by
        rw [hm_def]; exact Nat.pow_log_le_self (2 ^ S * W) (by omega)
      exact hprod_le.trans hpow_le_K
  -- Set up cluster index `I_cl`.
  obtain ⟨Q_set, hQ_def⟩ : ∃ Q_set : Finset (ℕ × ℕ), Q_set = oddPrimePowers P_max := ⟨_, rfl⟩
  have hC_card_pos : ∀ x : ℕ × ℕ, 0 < (clusterPrimes W S x.1).card := by
    intro x
    have := le_card_clusterPrimes (by omega : 1 ≤ W) S x.1
    omega
  obtain ⟨I_cl, hIcl_def⟩ : ∃ I_cl : Finset ((ℕ × ℕ) × (ℕ × ℕ)),
      I_cl = Q_set.biUnion (fun x =>
        ((clusterPrimes W S x.1) ×ˢ (clusterPrimes W S x.1)).map
          ⟨fun p => (x, p), fun _ _ h => (Prod.mk.inj h).2⟩) := ⟨_, rfl⟩
  have hmem_Icl : ∀ z : (ℕ × ℕ) × (ℕ × ℕ),
      z ∈ I_cl ↔ z.1 ∈ Q_set ∧ z.2.1 ∈ clusterPrimes W S z.1.1 ∧
        z.2.2 ∈ clusterPrimes W S z.1.1 := by
    intro ⟨x, p₁, p₂⟩
    rw [hIcl_def, mem_biUnion]
    constructor
    · rintro ⟨x', hx', hmap⟩
      rcases mem_map.mp hmap with ⟨⟨q₁, q₂⟩, hqq, heq⟩
      simp only [Function.Embedding.coeFn_mk, Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl, rfl⟩
      exact ⟨hx', (mem_product.mp hqq).1, (mem_product.mp hqq).2⟩
    · rintro ⟨hx, hp₁, hp₂⟩
      exact ⟨x, hx, mem_map.mpr ⟨(p₁, p₂), mem_product.mpr ⟨hp₁, hp₂⟩, rfl⟩⟩
  have hsum_Icl : ∀ φ : (ℕ × ℕ) × (ℕ × ℕ) → ℝ,
      ∑ z ∈ I_cl, φ z =
        ∑ x ∈ Q_set, ∑ p ∈ clusterPrimes W S x.1 ×ˢ clusterPrimes W S x.1, φ (x, p) := by
    intro φ
    rw [hIcl_def]
    have hdisj : (Q_set : Set (ℕ × ℕ)).PairwiseDisjoint fun x =>
        ((clusterPrimes W S x.1) ×ˢ (clusterPrimes W S x.1)).map
          ⟨fun p => (x, p), fun _ _ h => (Prod.mk.inj h).2⟩ := by
      intro x₁ _ x₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro z hz₁ hz₂
      rcases mem_map.mp hz₁ with ⟨_, _, rfl⟩
      rcases mem_map.mp hz₂ with ⟨_, _, heq⟩
      exact hne (Prod.mk.inj heq).1.symm
    rw [sum_biUnion hdisj]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_map]; rfl
  have hcl_bounds : ∀ x ∈ Q_set, ∀ p₁ ∈ clusterPrimes W S x.1, ∀ p₂ ∈ clusterPrimes W S x.1,
      2 ≤ hammingLetter K W S (x.1 ^ x.2) p₁ p₂ ∧
      hammingLetter K W S (x.1 ^ x.2) p₁ p₂ ≤ K ∧
      K < 2 ^ (2 * S + 1) * hammingLetter K W S (x.1 ^ x.2) p₁ p₂ ∧
      B₀ < hammingBase K W S (x.1 ^ x.2) p₁ := by
    intro x hx p₁ hp₁ p₂ hp₂
    rw [hQ_def, mem_oddPrimePowers_iff] at hx
    obtain ⟨_, hqp, _, hQP⟩ := hx
    have hQ1 : 1 ≤ x.1 ^ x.2 := pow_pos hqp.pos x.2
    have hb := hammingLetter_bounds hW hQ1 hQP (hS_def ▸ hK_sq)
      (clusterPrimes_subset W S x.1 hp₁) (clusterPrimes_subset W S x.1 hp₂)
    refine ⟨hb.1, hb.2.1, hb.2.2.1, ?_⟩
    have hexp_le : 2 * S + 1 ≤ S * (M₀ + 1) + 2 := by nlinarith
    have hden_le : 2 ^ (2 * S + 1) * W ≤ 2 ^ (S * (M₀ + 1) + 2) * W :=
      Nat.mul_le_mul_right W (Nat.pow_le_pow_right (by norm_num) hexp_le)
    rw [hB₀_def]
    exact (Nat.div_le_div_left hden_le (by positivity)).trans_lt (Nat.div_lt_of_lt_mul hb.2.2.2)
  -- Combined letter family `I_all`.
  obtain ⟨I_all, hI_def⟩ :
      ∃ I_all : Finset (ℕ ⊕ (((ℕ × ℕ) × (ℕ × ℕ)) ⊕ Finset ℕ)),
        I_all = (Icc 2 N).disjSum (I_cl.disjSum I_ramp) := ⟨_, rfl⟩
  obtain ⟨ℓ_fn, hℓ_def⟩ :
      ∃ ℓ_fn : ℕ ⊕ (((ℕ × ℕ) × (ℕ × ℕ)) ⊕ Finset ℕ) → ℕ,
        ℓ_fn = Sum.elim id (Sum.elim
          (fun z => hammingLetter K W S (z.1.1 ^ z.1.2) z.2.1 z.2.2)
          (fun A => A.prod id)) := ⟨_, rfl⟩
  obtain ⟨w_fn, hw_def⟩ :
      ∃ w_fn : ℕ ⊕ (((ℕ × ℕ) × (ℕ × ℕ)) ⊕ Finset ℕ) → ℚ,
        w_fn = Sum.elim
          (fun k => -(b k : ℚ) / (k : ℚ))
          (Sum.elim
            (fun z => ((16 * M₀ * K * tautDefect b N (z.1.1 ^ z.1.2) : ℕ) : ℚ) /
              ((B₀ * (clusterPrimes W S z.1.1).card ^ 2 *
                hammingLetter K W S (z.1.1 ^ z.1.2) z.2.1 z.2.2 : ℕ) : ℚ))
            (fun _ => 4 * Y_rat / (I_ramp.card : ℚ))) := ⟨_, rfl⟩
  have hℓ_bounds : ∀ u ∈ I_all, 2 ≤ ℓ_fn u ∧ ℓ_fn u ≤ K := by
    intro u hu
    rw [hI_def] at hu; rw [hℓ_def]
    rcases u with k | (z | A)
    · simp only [Sum.elim_inl, id]
      have hk : k ∈ Icc 2 N := by simpa using hu
      obtain ⟨hk2, hkN⟩ := mem_Icc.mp hk
      exact ⟨hk2, hkN.trans hNK⟩
    · simp only [Sum.elim_inr, Sum.elim_inl]
      have hz : z ∈ I_cl := by simpa using hu
      obtain ⟨hx, hp₁, hp₂⟩ := (hmem_Icl z).mp hz
      have hb := hcl_bounds z.1 hx z.2.1 hp₁ z.2.2 hp₂
      exact ⟨hb.1, hb.2.1⟩
    · simp only [Sum.elim_inr]
      have hA : A ∈ I_ramp := by simpa using hu
      obtain ⟨hgt, hle⟩ := hramp_bounds A hA
      exact ⟨by omega, hle⟩
  obtain ⟨c, D_den, hD_pos, hc0, hbal, hstep, hslope, hsupp⟩ :=
    exists_stencil_of_family I_all ℓ_fn w_fn (fun u hu => (hℓ_bounds u hu).1)
  have hDR_pos : (0 : ℝ) < (D_den : ℝ) := by exact_mod_cast hD_pos
  -- Split any test function `φ` across near, cluster, and ramp letters.
  have hsplit_φ : ∀ φ : ℕ → ℝ,
      ∑ u ∈ I_all, (w_fn u : ℝ) * φ (ℓ_fn u) =
        (∑ k ∈ Icc 2 N, (-(b k : ℝ) / k) * φ k) +
        (∑ x ∈ Q_set,
          ((16 * (M₀ : ℝ) * (K : ℝ) / (B₀ : ℝ)) * (tautDefect b N (x.1 ^ x.2) : ℝ)) *
            ((1 / ((clusterPrimes W S x.1).card ^ 2 : ℝ)) *
              ∑ p ∈ clusterPrimes W S x.1 ×ˢ clusterPrimes W S x.1,
                φ (hammingLetter K W S (x.1 ^ x.2) p.1 p.2) /
                  (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ))) +
        ((4 * (Y_rat : ℝ) / (I_ramp.card : ℝ)) * ∑ A ∈ I_ramp, φ (A.prod id)) := by
    intro φ
    rw [hI_def, sum_disjSum, sum_disjSum, add_assoc]
    congr 1
    · refine sum_congr rfl fun k _ => ?_
      rw [hw_def, hℓ_def]; simp only [Sum.elim_inl, id]; push_cast; rfl
    · congr 1
      · rw [hsum_Icl]
        refine sum_congr rfl fun x hx => ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun p hp => ?_
        obtain ⟨hp₁, hp₂⟩ := mem_product.mp hp
        have hL_pos : (0 : ℝ) < (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) := by
          exact_mod_cast (by have := (hcl_bounds x hx p.1 hp₁ p.2 hp₂).1; omega)
        have hC_ne : ((clusterPrimes W S x.1).card : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (hC_card_pos x).ne'
        rw [hw_def, hℓ_def]; simp only [Sum.elim_inr, Sum.elim_inl]
        push_cast
        field_simp [hBR_pos.ne', hC_ne, hL_pos.ne']
      · rw [mul_sum]
        refine sum_congr rfl fun A _ => ?_
        have hcard_ne : (I_ramp.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hIramp_pos.ne'
        rw [hw_def, hℓ_def]; simp only [Sum.elim_inr]
        push_cast
        field_simp [hcard_ne]
  have hval_r : ∀ r : ℕ,
      ∑ u ∈ I_all, (w_fn u : ℝ) * ((r % ℓ_fn u : ℕ) : ℝ) =
        tautNear b N r + (∑ x ∈ Q_set, hammingClusterTerm b N K W S M₀ B₀ x r) +
          hammingRampTerm Y_rat I_ramp r := by
    intro r
    rw [hsplit_φ fun k => ((r % k : ℕ) : ℝ), tautNear]
    rfl
  have hnear_X : ∀ s : ℕ, 1 ≤ s → s ≤ X → |tautNear b N s - 1| ≤ (s : ℝ) * Y_n :=
    fun s hs1 hsX => abs_tautNear_sub_one_le (by omega) hb1 hb_supp hη₀ hB_mert hs1 hsX
  have hB₀_le_K : B₀ ≤ K := Nat.div_le_self _ _
  have hB₀_le_X : B₀ ≤ X := hB₀_le_K.trans hKX
  -- Assemble `IsProducer c D_den B₀`, `AlphabetLE c K`, and the rate bound.
  have hP : IsProducer c D_den B₀ := by
    refine ⟨hc0, hbal, fun r => ?_, hD_pos, hB₀2, fun r hr => ?_⟩
    · have hR : (0 : ℝ) ≤ (stepWeight c r : ℝ) := by
        rw [hstep r, hval_r r]
        exact mul_nonneg hDR_pos.le
          (hammingTotal_nonneg hN2 hb2 hb_smooth hM₀ hW hK_pos hB₀_pos hS_def (hS_def ▸ hK_sq)
            hm_lo hm_hi hP_def hP_card_ge hm_le_P hQ_def hIramp_def hIramp_pos hC_card_pos
            hramp_bounds hcl_bounds hYn_pos.le hYrat_nn hYrat_ge hB₀_le_X hnear_X r)
      exact_mod_cast hR
    · obtain ⟨hr1, hr2⟩ := mem_Ico.mp hr
      have hR : ((D_den : ℤ) : ℝ) ≤ (stepWeight c r : ℝ) := by
        rw [hstep r, hval_r r]
        push_cast
        calc (D_den : ℝ) = (D_den : ℝ) * 1 := (mul_one _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left
              (hammingTotal_win_ge_one hYrat_nn hYrat_ge hIramp_pos hramp_bounds hB₀_le_X hnear_X hr1 hr2)
              hDR_pos.le
      exact_mod_cast hR
  have halph : AlphabetLE c K := by
    intro k hk
    rcases mem_insert.mp (hsupp hk) with rfl | hmem
    · omega
    · obtain ⟨u, hu, rfl⟩ := mem_image.mp hmem
      exact (hℓ_bounds u hu).2
  refine ⟨c, D_den, hP, halph, ?_⟩
  have hlogK_nn : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ K))
  have hslope_near : tautSlope b N ≤
      1 - 1 / (B₀ : ℝ) + Y_n * (1 + Real.log (B₀ : ℝ)) + tautMass b N / (B₀ : ℝ) :=
    tautSlope_le hB₀2 hYn_pos.le fun s hs1 hsB => hnear_X s hs1 (hsB.le.trans hB₀_le_X)
  have hslope_cl : ∑ x ∈ Q_set,
      ((16 * (M₀ : ℝ) * (K : ℝ) / (B₀ : ℝ)) * (tautDefect b N (x.1 ^ x.2) : ℝ)) *
        ((1 / ((clusterPrimes W S x.1).card ^ 2 : ℝ)) *
          ∑ p ∈ clusterPrimes W S x.1 ×ˢ clusterPrimes W S x.1,
            Real.log (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ) /
              (hammingLetter K W S (x.1 ^ x.2) p.1 p.2 : ℝ)) ≤
      (16 * (M₀ : ℝ) * (2 ^ (2 * S + 1) : ℝ) * Real.log (K : ℝ) / (B₀ : ℝ)) *
        ((Nat.log 2 N : ℝ) + 1) ^ 2 * tautMass b N := by
    rw [hQ_def]
    exact hammingCluster_slope_le (by omega) hB₀_pos hC_card_pos
      (fun x hx p₁ hp₁ p₂ hp₂ =>
        ⟨(hcl_bounds x (hQ_def.symm ▸ hx) p₁ hp₁ p₂ hp₂).1,
         (hcl_bounds x (hQ_def.symm ▸ hx) p₁ hp₁ p₂ hp₂).2.1,
         (hcl_bounds x (hQ_def.symm ▸ hx) p₁ hp₁ p₂ hp₂).2.2.1⟩)
  have hslope_ramp : (4 * (Y_rat : ℝ) / (I_ramp.card : ℝ)) *
      (∑ A ∈ I_ramp, Real.log ((A.prod id : ℕ) : ℝ)) ≤ 8 * Y_n * Real.log (K : ℝ) := by
    have hlog_A : ∀ A ∈ I_ramp, Real.log ((A.prod id : ℕ) : ℝ) ≤ Real.log (K : ℝ) := by
      intro A hA
      obtain ⟨hgt, hle⟩ := hramp_bounds A hA
      have hpos : (0 : ℝ) < ((A.prod id : ℕ) : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le hB₀_pos hgt.le)
      exact Real.log_le_log hpos (by exact_mod_cast hle)
    have hcard_ne : (I_ramp.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hIramp_pos.ne'
    calc (4 * (Y_rat : ℝ) / (I_ramp.card : ℝ)) * (∑ A ∈ I_ramp, Real.log ((A.prod id : ℕ) : ℝ))
        ≤ (4 * (Y_rat : ℝ) / (I_ramp.card : ℝ)) * ((I_ramp.card : ℝ) * Real.log (K : ℝ)) :=
          mul_le_mul_of_nonneg_left
            ((sum_le_sum hlog_A).trans_eq (by rw [sum_const, nsmul_eq_mul])) (by positivity)
      _ = 4 * (Y_rat : ℝ) * Real.log (K : ℝ) := by field_simp [hcard_ne]
      _ ≤ 8 * Y_n * Real.log (K : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith only [hYrat_le]) hlogK_nn
  set E_tot := Y_n * (1 + Real.log (B₀ : ℝ)) + 8 * Y_n * Real.log (K : ℝ) +
    tautMass b N / (B₀ : ℝ) +
    (16 * (M₀ : ℝ) * (2 ^ (2 * S + 1) : ℝ) * Real.log (K : ℝ) / (B₀ : ℝ)) *
      ((Nat.log 2 N : ℝ) + 1) ^ 2 * tautMass b N
  have hE_nn : 0 ≤ E_tot := by
    dsimp [E_tot]; have := tautMass_nonneg b N; positivity
  refine rate_le_of_slope_le' hP hE_nn ?_
  rw [hslope, hsplit_φ fun k => Real.log (k : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ hDR_pos.le
  change tautSlope b N + _ + _ ≤ 1 - 1 / (B₀ : ℝ) + E_tot
  dsimp [E_tot]
  linarith only [hslope_near, hslope_cl, hslope_ramp]

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
