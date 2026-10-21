import GaloisForLFunctions.BezoutValuationIncidence.KernelMeanAtCompositeModuliAndTheAllRowsLaws

/-!
# Sharp cutoffs stop the Type-I gain at `θ = 4/3`

The flat large-scale row `c'(n) = n` on `I = [A + 1, A + L]` (`b_n = 1`) reaches diagonal quality for
`A ≥ P^{3/2}`. Here it is shown that its sharp cutoff prevents more.

**The boundary term.** Let `G_p(n) = Σ_{k < n} (𝔅(p, k) - m_p)` be the periodic primitive of the
centred kernel. One summation by parts gives

`Λ_p(c') ≥ (G_p((A + L + 1) mod p) - G_p((A + 1) mod p))/(A + L) - (3/2) p³ L/(A + 1)²`.

The primitive is small near `0`, `|G_p(b)| ≤ b p²/4`, and large after the coherent stretch: for
`32 a ≤ p`, `G_p(a) ≥ a p²/50`. If `8192 ((A + 1) mod p) ≤ p` and `(A + L + 1) mod p ∈ [p/64, p/32]`
then `G_p(a) - G_p(b) ≥ p³/3600`. With `L ≤ (A + 1)/50000`,

`Λ_p(c') ≥ p³/(14400 A)`.

**Pigeonholes.** A periodic residue condition of density `1/K` holds, for some shift in any interval of
length `2D`, for a `1/(2K)` share of any set of moduli in `[1, D]`. Two nested shifts give, for every set
`S` of primes in `[256, D]`, an interval `I` with `|S| ≤ 2²² |S'|`, so that both endpoints are placed
for all `p ∈ S'`.

**Conclusion.** By the attained dual norm, some `|c| ≤ 1` on `S'` has

`B + m R' + β H' - main(c) ≥ Σ_{p ∈ S'} p²/(14400 A) - 6 (Σ_{p ∈ S'} p³) Σ_{n ∈ I} 1/n³`.

For primes `S' ≍ P/log P` and `L ≍ A` this is `≍ P³/(A log P)`, against the diagonal
`√(D(a) D(b)) ≍ A/√(log P)`. It exceeds the diagonal for `A ≤ c P^{3/2}`. Sharp-cutoff Type-I rows at the
large scale reach exactly `θ = 4/3`. The replacement is one order of smoothness, which reaches `θ = 3/2`.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. A density pigeonhole -/

theorem card_filter_Ico_ge_of_density {d K : ℕ} (hd : 0 < d) (P : ℕ → Prop) [DecidablePred P]
    (hper : Function.Periodic P d) (hdens : d ≤ K * Nat.count P d) (Q T : ℕ) :
    T ≤ d + K * ((Ico Q (Q + T)).filter P).card := by
  have hblock := card_filter_Ico_mul_eq P hper Q (T / d)
  have hmono : ((Ico Q (Q + T / d * d)).filter P).card ≤ ((Ico Q (Q + T)).filter P).card :=
    card_le_card (filter_subset_filter _ (Ico_subset_Ico_right (by
      have := Nat.div_mul_le_self T d; omega)))
  have hT : T ≤ d + T / d * d := by
    have := Nat.div_add_mod T d
    have := Nat.mod_lt T hd
    nlinarith
  calc T ≤ d + T / d * d := hT
    _ ≤ d + T / d * (K * Nat.count P d) := by gcongr
    _ = d + K * ((Ico Q (Q + T / d * d)).filter P).card := by rw [hblock]; ring
    _ ≤ d + K * ((Ico Q (Q + T)).filter P).card := by gcongr

/-- **The density pigeonhole.** If for every `d ∈ S ⊆ [1, D]` the `d`-periodic condition `P d` holds
for at least `d/K` residues, some `n₀ ∈ [Q, Q + 2D)` satisfies it for a `1/(2K)` share of `S`. -/
theorem exists_shift_of_density {S : Finset ℕ} {D K : ℕ} (hD : 0 < D)
    (hS : ∀ d ∈ S, 0 < d ∧ d ≤ D) (P : ℕ → ℕ → Prop) [∀ d, DecidablePred (P d)]
    (hper : ∀ d ∈ S, Function.Periodic (P d) d) (hdens : ∀ d ∈ S, d ≤ K * Nat.count (P d) d)
    (Q : ℕ) :
    ∃ n₀ ∈ Ico Q (Q + 2 * D), S.card ≤ 2 * K * (S.filter fun d => P d n₀).card := by
  classical
  have hne : (Ico Q (Q + 2 * D)).Nonempty := nonempty_Ico.mpr (by omega)
  refine exists_le_of_sum_le hne ?_
  have hswap : ∑ n₀ ∈ Ico Q (Q + 2 * D), (S.filter fun d => P d n₀).card =
      ∑ d ∈ S, ((Ico Q (Q + 2 * D)).filter fun n₀ => P d n₀).card := by
    simp only [card_filter]
    exact sum_comm
  have hd : ∀ d ∈ S, D ≤ K * ((Ico Q (Q + 2 * D)).filter fun n₀ => P d n₀).card :=
    fun d hdS => by
      have h1 := card_filter_Ico_ge_of_density (hS d hdS).1 (P d) (hper d hdS) (hdens d hdS) Q
        (2 * D)
      have h2 : ((Ico Q (Q + 2 * D)).filter fun n₀ => P d n₀).card =
          ((Ico Q (Q + 2 * D)).filter (P d)).card := rfl
      rw [← h2] at h1
      have := (hS d hdS).2
      omega
  rw [← mul_sum, hswap, sum_const, Nat.card_Ico, smul_eq_mul, show Q + 2 * D - Q = 2 * D by omega]
  calc 2 * D * S.card = 2 * ∑ _d ∈ S, D := by rw [sum_const, smul_eq_mul]; ring
    _ ≤ 2 * ∑ d ∈ S, K * ((Ico Q (Q + 2 * D)).filter fun n₀ => P d n₀).card :=
        Nat.mul_le_mul_left _ (sum_le_sum hd)
    _ = 2 * K * ∑ d ∈ S, ((Ico Q (Q + 2 * D)).filter fun n₀ => P d n₀).card := by
        rw [← mul_sum]; ring

/-! ## §2. Two residue windows -/

/-- The window `[0, d/8192]`. -/
def nearZeroWindow (d n : ℕ) : Prop := 8192 * (n % d) ≤ d

/-- The window `[d/64, d/32]`. -/
def coherentEndWindow (d n : ℕ) : Prop := d ≤ 64 * (n % d) ∧ 32 * (n % d) ≤ d

instance (d n : ℕ) : Decidable (nearZeroWindow d n) := by unfold nearZeroWindow; infer_instance
instance (d n : ℕ) : Decidable (coherentEndWindow d n) := by unfold coherentEndWindow; infer_instance

theorem nearZeroWindow_periodic (d : ℕ) : Function.Periodic (nearZeroWindow d) d := fun n => by
  simp only [nearZeroWindow, Nat.add_mod_right]

theorem coherentEndWindow_periodic (d : ℕ) : Function.Periodic (coherentEndWindow d) d := fun n => by
  simp only [coherentEndWindow, Nat.add_mod_right]

theorem le_count_nearZeroWindow {d : ℕ} (hd : 0 < d) : d ≤ 8192 * Nat.count (nearZeroWindow d) d := by
  have hc : Nat.count (nearZeroWindow d) d = ((range d).filter (nearZeroWindow d)).card :=
    Nat.count_eq_card_filter_range _ _
  rw [hc]
  have hsub : range (d / 8192 + 1) ⊆ (range d).filter (nearZeroWindow d) := by
    intro x hx
    have hx' := mem_range.mp hx
    have hxd : x < d := by omega
    simp only [mem_filter, mem_range, nearZeroWindow, Nat.mod_eq_of_lt hxd]
    exact ⟨hxd, by omega⟩
  have := card_le_card hsub
  rw [card_range] at this
  omega

theorem le_count_coherentEndWindow {d : ℕ} (hd : 256 ≤ d) :
    d ≤ 128 * Nat.count (coherentEndWindow d) d := by
  have hc : Nat.count (coherentEndWindow d) d = ((range d).filter (coherentEndWindow d)).card :=
    Nat.count_eq_card_filter_range _ _
  rw [hc]
  set lo := (d + 63) / 64
  have hsub : Ico lo (lo + (d / 128 + 1)) ⊆ (range d).filter (coherentEndWindow d) := by
    intro x hx
    have hx' := mem_Ico.mp hx
    have hxd : x < d := by omega
    simp only [mem_filter, mem_range, coherentEndWindow, Nat.mod_eq_of_lt hxd]
    exact ⟨hxd, by omega, by omega⟩
  have := card_le_card hsub
  rw [Nat.card_Ico] at this
  omega

/-! ## §3. The primitive of the centred kernel -/

/-- `G_p(n) = Σ_{k < n} (𝔅(p, k) - m_p)`. -/
def centredKernelPrimitive (p n : ℕ) : ℝ := ∑ k ∈ range n, (bernoulliKernel p k - primeKernelMean p)

theorem centredKernelPrimitive_periodic {p : ℕ} (hp : p.Prime) :
    Function.Periodic (centredKernelPrimitive p) p := fun n => by
  simp only [centredKernelPrimitive]
  rw [← sum_range_add_sum_Ico _ (by omega : n ≤ n + p),
    sum_Ico_eq_sum_range_of_periodic (fun k => by simp only [bernoulliKernel_add_period]) n,
    sum_range_bernoulliKernel_sub_mean hp, add_zero]

theorem abs_centredKernelPrimitive_le {p : ℕ} (hp : p.Prime) (n : ℕ) :
    |centredKernelPrimitive p n| ≤ (p : ℝ) ^ 3 / 4 := by
  have h := abs_sum_Ico_le_of_periodic hp.pos (g := fun k => bernoulliKernel p k - primeKernelMean p)
    (fun k => by simp only [bernoulliKernel_add_period]) (sum_range_bernoulliKernel_sub_mean hp)
    (B := (p : ℝ) ^ 2 / 4) (abs_bernoulliKernel_sub_mean_le hp) 0 n
  rw [zero_add, ← range_eq_Ico] at h
  calc |centredKernelPrimitive p n| ≤ p * ((p : ℝ) ^ 2 / 4) := h
    _ = (p : ℝ) ^ 3 / 4 := by ring

theorem abs_centredKernelPrimitive_le_small {p : ℕ} (hp : p.Prime) (b : ℕ) :
    |centredKernelPrimitive p b| ≤ b * ((p : ℝ) ^ 2 / 4) := by
  unfold centredKernelPrimitive
  calc |∑ k ∈ range b, (bernoulliKernel p k - primeKernelMean p)|
      ≤ ∑ k ∈ range b, |bernoulliKernel p k - primeKernelMean p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ range b, (p : ℝ) ^ 2 / 4 := sum_le_sum fun k _ => abs_bernoulliKernel_sub_mean_le hp k
    _ = b * ((p : ℝ) ^ 2 / 4) := by rw [sum_const, card_range, nsmul_eq_mul]

theorem centredKernelPrimitive_ge_coherent {p a : ℕ} (hp : p.Prime) (hp64 : 64 ≤ p)
    (ha : 32 * a ≤ p) : a * ((p : ℝ) ^ 2 / 50) ≤ centredKernelPrimitive p a := by
  unfold centredKernelPrimitive
  have hpi : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hm : primeKernelMean p ≤ Real.pi ^ 2 / 72 := by
    unfold primeKernelMean
    have hp2 : (1 : ℝ) ≤ (p : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      nlinarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos, sq_nonneg Real.pi]
  have hpR : (64 : ℝ) ≤ p := by exact_mod_cast hp64
  calc a * ((p : ℝ) ^ 2 / 50) = ∑ _k ∈ range a, (p : ℝ) ^ 2 / 50 := by
        rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ ∑ k ∈ range a, (bernoulliKernel p k - primeKernelMean p) := by
        refine sum_le_sum fun k hk => ?_
        have hk' := mem_range.mp hk
        have hkp : k % p = k := Nat.mod_eq_of_lt (by omega)
        have h32 : 32 * (k % p) ≤ p := by rw [hkp]; omega
        have hb := bernoulliKernel_ge hp.pos h32
        nlinarith

/-! ## §4. The kernel statistic of a flat row -/

theorem sum_Ico_inv_sub_inv_succ {a b : ℕ} (hab : a ≤ b) :
    ∑ M ∈ Ico a b, (1 / (M : ℝ) - 1 / ((M + 1 : ℕ) : ℝ)) = 1 / (a : ℝ) - 1 / (b : ℝ) := by
  have := sum_Ico_sub (fun M : ℕ => -(1 / (M : ℝ))) hab
  simp only [neg_sub_neg] at this
  rw [← this]

/-- **The boundary term of a sharp cutoff.** For the flat row on `[A + 1, A + L]`, `1 ≤ L`, `A + L ≤ N`:
`Λ_p ≥ (G_p((A + L + 1) mod p) - G_p((A + 1) mod p))/(A + L) - (3/2) p³ L/(A + 1)²`. -/
theorem kernelStatistic_flatLargeRow_ge {N A L p : ℕ} (hp : p.Prime) (hL : 1 ≤ L)
    (hAL : A + L ≤ N) :
    (centredKernelPrimitive p ((A + L + 1) % p) - centredKernelPrimitive p ((A + 1) % p)) /
        ((A : ℝ) + L) - 3 / 2 * (p : ℝ) ^ 3 * L / ((A : ℝ) + 1) ^ 2 ≤
      kernelStatistic N (flatLargeRow A L) p := by
  have hsub : Icc (A + 1) (A + L) ⊆ Icc 1 N := Icc_subset_Icc (by omega) hAL
  have hA1 : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  have hAL0 : (0 : ℝ) < (A : ℝ) + L := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    positivity
  set G := centredKernelPrimitive p
  set D : ℕ → ℝ := fun n => bernoulliKernel p n - primeKernelMean p
  have hG : ∀ n, G (n + 1) - G n = D n := fun n => by
    simp only [G, D, centredKernelPrimitive, Finset.sum_range_succ]; ring
  have hper := centredKernelPrimitive_periodic hp
  have hGb := abs_centredKernelPrimitive_le hp
  -- restrict to the interval
  have hre : kernelStatistic N (flatLargeRow A L) p =
      ∑ n ∈ Ico (A + 1) (A + 1 + (L - 1) + 1), D n * (1 / (n : ℝ)) +
        ∑ n ∈ Icc (A + 1) (A + L), cubicKernel p n / (n : ℝ) ^ 2 := by
    rw [kernelStatistic, ← sum_subset hsub fun n _ hn => by simp [flatLargeRow, hn],
      show A + 1 + (L - 1) + 1 = A + L + 1 by omega,
      show Ico (A + 1) (A + L + 1) = Icc (A + 1) (A + L) by
        ext; simp only [mem_Ico, mem_Icc]; omega,
      ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by have := mem_Icc.mp hn; omega : 0 < n)
    rw [flatLargeRow, if_pos hn]
    simp only [D]
    field_simp
  rw [hre]
  -- the quadratic part by one summation by parts
  set u : ℕ → ℝ := fun M => 1 / (M : ℝ)
  have hparts := sum_Ico_sub_mul_eq G u (A + 1) (L - 1)
  have hX : ∑ n ∈ Ico (A + 1) (A + 1 + (L - 1) + 1), D n * (1 / (n : ℝ)) =
      G (A + 1 + (L - 1) + 1) * u (A + 1 + (L - 1)) - G (A + 1) * u (A + 1) +
        ∑ M ∈ Ico (A + 1) (A + 1 + (L - 1)), G (M + 1) * (u M - u (M + 1)) := by
    rw [← hparts]
    exact sum_congr rfl fun n _ => by rw [hG]
  rw [hX]
  set R := ∑ M ∈ Ico (A + 1) (A + 1 + (L - 1)), G (M + 1) * (u M - u (M + 1))
  have htel : ∑ M ∈ Ico (A + 1) (A + 1 + (L - 1)), (u M - u (M + 1)) =
      1 / ((A : ℝ) + 1) - 1 / ((A : ℝ) + L) := by
    simp only [u]
    rw [sum_Ico_inv_sub_inv_succ (by omega), show A + 1 + (L - 1) = A + L by omega]
    push_cast; ring
  have hdiff : 1 / ((A : ℝ) + 1) - 1 / ((A : ℝ) + L) ≤ L / ((A : ℝ) + 1) ^ 2 := by
    rw [div_sub_div _ _ hA1.ne' hAL0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have h2 : 0 ≤ (L : ℝ) ^ 2 - L + A + 1 := by nlinarith
    nlinarith [mul_nonneg hA1.le h2]
  have hdiff0 : 0 ≤ 1 / ((A : ℝ) + 1) - 1 / ((A : ℝ) + L) := by
    rw [sub_nonneg]
    refine one_div_le_one_div_of_le hA1 ?_
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hR : |R| ≤ (p : ℝ) ^ 3 / 4 * (1 / ((A : ℝ) + 1) - 1 / ((A : ℝ) + L)) := by
    rw [← htel, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun M hM => ?_)
    have hM1 : 1 ≤ M := by have := mem_Ico.mp hM; omega
    have hu : 0 ≤ u M - u (M + 1) := by
      simp only [u]
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (by exact_mod_cast hM1) (by push_cast; linarith)
    rw [abs_mul, abs_of_nonneg hu]
    exact mul_le_mul_of_nonneg_right (hGb _) hu
  -- the cubic part crudely
  have hY : -((p : ℝ) ^ 3 * L / ((A : ℝ) + 1) ^ 2) ≤
      ∑ n ∈ Icc (A + 1) (A + L), cubicKernel p n / (n : ℝ) ^ 2 := by
    have hb : ∀ n ∈ Icc (A + 1) (A + L), -((p : ℝ) ^ 3 / ((A : ℝ) + 1) ^ 2) ≤
        cubicKernel p n / (n : ℝ) ^ 2 := fun n hn => by
      have hn1 : (A : ℝ) + 1 ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by linarith
      have hk := abs_cubicKernel_le hp.pos n
      have h1 : |cubicKernel p n / (n : ℝ) ^ 2| ≤ (p : ℝ) ^ 3 / ((A : ℝ) + 1) ^ 2 := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
        calc |cubicKernel p n| / (n : ℝ) ^ 2 ≤ (p : ℝ) ^ 3 / (n : ℝ) ^ 2 :=
              div_le_div_of_nonneg_right hk (by positivity)
          _ ≤ (p : ℝ) ^ 3 / ((A : ℝ) + 1) ^ 2 :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
      exact (abs_le.mp h1).1
    calc -((p : ℝ) ^ 3 * L / ((A : ℝ) + 1) ^ 2) =
          ∑ _n ∈ Icc (A + 1) (A + L), -((p : ℝ) ^ 3 / ((A : ℝ) + 1) ^ 2) := by
          rw [sum_const, Nat.card_Icc, show A + L + 1 - (A + 1) = L by omega, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum hb
  -- the boundary values through periodicity
  have hGa : G (A + 1 + (L - 1) + 1) = G ((A + L + 1) % p) := by
    rw [show A + 1 + (L - 1) + 1 = A + L + 1 by omega]
    exact (hper.map_mod_nat _).symm
  have hGb' : G (A + 1) = G ((A + 1) % p) := (hper.map_mod_nat _).symm
  have hu1 : u (A + 1 + (L - 1)) = 1 / ((A : ℝ) + L) := by
    simp only [u]; rw [show A + 1 + (L - 1) = A + L by omega]; push_cast; ring
  have hu2 : u (A + 1) = 1 / ((A : ℝ) + 1) := by simp only [u]; push_cast; ring
  rw [hGa, hGb', hu1, hu2]
  set a := G ((A + L + 1) % p)
  set b := G ((A + 1) % p)
  have hbb : |b| ≤ (p : ℝ) ^ 3 / 4 := hGb _
  have key : a * (1 / ((A : ℝ) + L)) - b * (1 / ((A : ℝ) + 1)) =
      (a - b) / ((A : ℝ) + L) - b * (1 / ((A : ℝ) + 1) - 1 / ((A : ℝ) + L)) := by
    field_simp; ring
  have hbterm : b * (1 / ((A : ℝ) + 1) - 1 / ((A : ℝ) + L)) ≤
      (p : ℝ) ^ 3 / 4 * (1 / ((A : ℝ) + 1) - 1 / ((A : ℝ) + L)) := by
    have := mul_le_mul_of_nonneg_right ((le_abs_self b).trans hbb) hdiff0
    linarith
  have hRl := (abs_le.mp hR).1
  have hp3 : (0 : ℝ) ≤ (p : ℝ) ^ 3 := by positivity
  have h1 : (p : ℝ) ^ 3 / 4 * (1 / ((A : ℝ) + 1) - 1 / ((A : ℝ) + L)) ≤
      (p : ℝ) ^ 3 / 4 * (L / ((A : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left hdiff (by positivity)
  have h2 : 3 / 2 * (p : ℝ) ^ 3 * L / ((A : ℝ) + 1) ^ 2 =
      2 * ((p : ℝ) ^ 3 / 4 * (L / ((A : ℝ) + 1) ^ 2)) + (p : ℝ) ^ 3 * L / ((A : ℝ) + 1) ^ 2 := by ring
  rw [key]
  linarith

/-! ## §5. The configuration -/

/-- **Sharp cutoffs stop at `θ = 4/3`.** For every set `S` of primes in `[256, D]`, `0 < D`, every
`1 ≤ L₀`, `Q ≥ 50000 (L₀ + 2D)` and `N ≥ Q + 4D + L₀`, there are `A, L` with `Q ≤ A + 1 < Q + 2D`,
`L₀ ≤ L < L₀ + 2D`, a subset `S' ⊆ S` with `|S| ≤ 2²² |S'|`, and a row `|c| ≤ 1` on `S'` with
`B(c, c') + m R' + β H' - main(c) ≥ Σ_{p ∈ S'} p²/(14400 A) - 6 (Σ_{p ∈ S'} p³) Σ_n |c'(n)|/n⁴`
for the flat row `c'` on `[A + 1, A + L]`. -/
theorem exists_sharp_cutoff_configuration {S : Finset ℕ} {D Q L₀ N : ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ 256 ≤ p ∧ p ≤ D) (hD : 0 < D) (hL₀ : 1 ≤ L₀)
    (hQ : 50000 * (L₀ + 2 * D) ≤ Q) (hN : Q + 4 * D + L₀ ≤ N) :
    ∃ A L : ℕ, Q ≤ A + 1 ∧ A + 1 < Q + 2 * D ∧ L₀ ≤ L ∧ L < L₀ + 2 * D ∧ A + L ≤ N ∧
      ∃ S' ⊆ S, S.card ≤ 2 ^ 22 * S'.card ∧
        ∃ c : ℕ → ℝ, (∀ d, |c d| ≤ 1) ∧ (∀ d, c d ≠ 0 → d ∈ S') ∧
          ∑ p ∈ S', (p : ℝ) ^ 2 / (14400 * A) -
              6 * (∑ p ∈ S', (p : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |flatLargeRow A L n| / (n : ℝ) ^ 4 ≤
            rowBilinear N c (flatLargeRow A L) +
              rowMean N c * vonMangoldtReadout N (flatLargeRow A L) +
              rowBeta N c * finiteHarmonicSum N (flatLargeRow A L) -
              equidistributedMain N c (flatLargeRow A L) := by
  classical
  -- the left endpoint near a multiple
  obtain ⟨n₀, hn₀, hcard₁⟩ := exists_shift_of_density (K := 8192) hD
    (fun d hd => ⟨(hS d hd).1.pos, (hS d hd).2.2⟩) nearZeroWindow
    (fun d _ => nearZeroWindow_periodic d) (fun d hd => le_count_nearZeroWindow (hS d hd).1.pos) Q
  set S₁ := S.filter fun d => nearZeroWindow d n₀
  -- the right endpoint after the coherent stretch
  obtain ⟨n₁, hn₁, hcard₂⟩ := exists_shift_of_density (S := S₁) (K := 128) hD
    (fun d hd => ⟨(hS d (mem_filter.mp hd).1).1.pos, (hS d (mem_filter.mp hd).1).2.2⟩)
    coherentEndWindow (fun d _ => coherentEndWindow_periodic d)
    (fun d hd => le_count_coherentEndWindow (hS d (mem_filter.mp hd).1).2.1) (n₀ + L₀)
  set S₂ := S₁.filter fun d => coherentEndWindow d n₁
  have b₀ := mem_Ico.mp hn₀
  have b₁ := mem_Ico.mp hn₁
  set A := n₀ - 1
  set L := n₁ - n₀
  have hA1 : A + 1 = n₀ := by omega
  have hAL1 : A + L + 1 = n₁ := by omega
  have hLb : L₀ ≤ L ∧ L < L₀ + 2 * D := ⟨by omega, by omega⟩
  have hALN : A + L ≤ N := by omega
  have hS₂ : ∀ p ∈ S₂, p.Prime ∧ p ≤ N := fun p hp => by
    have := (hS p (mem_filter.mp (mem_filter.mp hp).1).1)
    exact ⟨this.1, by omega⟩
  obtain ⟨c, hc1, hsupp, hge⟩ := exists_rowBilinear_sub_main_ge N hS₂ (flatLargeRow A L)
  refine ⟨A, L, by omega, by omega, hLb.1, hLb.2, hALN, S₂,
    fun p hp => (mem_filter.mp (mem_filter.mp hp).1).1, ?_, c, hc1, hsupp, ?_⟩
  · calc S.card ≤ 2 * 8192 * S₁.card := hcard₁
      _ ≤ 2 * 8192 * (2 * 128 * S₂.card) := Nat.mul_le_mul_left _ hcard₂
      _ = 2 ^ 22 * S₂.card := by ring
  -- each statistic is at least `p³/(14400 A)`
  have hAR : (50000 : ℝ) ≤ (A : ℝ) + 1 := by
    have : 50000 ≤ A + 1 := by omega
    exact_mod_cast this
  have hLR : (L : ℝ) * 50000 ≤ (A : ℝ) + 1 := by
    have : L * 50000 ≤ A + 1 := by omega
    exact_mod_cast this
  have hL1R : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hstat : ∀ p ∈ S₂, (p : ℝ) ^ 2 / (14400 * A) ≤ |kernelStatistic N (flatLargeRow A L) p| / p := by
    intro p hp
    obtain ⟨hp₁, hcoh⟩ := mem_filter.mp hp
    obtain ⟨hpS, hnear⟩ := mem_filter.mp hp₁
    obtain ⟨hpp, hp256, -⟩ := hS p hpS
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlow := kernelStatistic_flatLargeRow_ge (N := N) hpp (by omega) hALN
    rw [hA1, hAL1] at hlow
    -- the boundary values
    have hb := abs_centredKernelPrimitive_le_small hpp (n₀ % p)
    have hbR : ((n₀ % p : ℕ) : ℝ) * 8192 ≤ p := by
      have : n₀ % p * 8192 ≤ p := by simp only [nearZeroWindow] at hnear; omega
      exact_mod_cast this
    obtain ⟨hc1', hc2'⟩ := hcoh
    have ha := centredKernelPrimitive_ge_coherent hpp (by omega) hc2'
    have haR : (p : ℝ) ≤ 64 * ((n₁ % p : ℕ) : ℝ) := by exact_mod_cast hc1'
    have hGa : (p : ℝ) ^ 3 / 3200 ≤ centredKernelPrimitive p (n₁ % p) := by
      have : (p : ℝ) / 64 * ((p : ℝ) ^ 2 / 50) ≤ ((n₁ % p : ℕ) : ℝ) * ((p : ℝ) ^ 2 / 50) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith [show (p : ℝ) / 64 * ((p : ℝ) ^ 2 / 50) = (p : ℝ) ^ 3 / 3200 by ring]
    have hGb : centredKernelPrimitive p (n₀ % p) ≤ (p : ℝ) ^ 3 / 32768 := by
      have h1 := (abs_le.mp hb).2
      have : ((n₀ % p : ℕ) : ℝ) * ((p : ℝ) ^ 2 / 4) ≤ (p : ℝ) / 8192 * ((p : ℝ) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith [show (p : ℝ) / 8192 * ((p : ℝ) ^ 2 / 4) = (p : ℝ) ^ 3 / 32768 by ring]
    have hdiffG : (p : ℝ) ^ 3 / 3600 ≤
        centredKernelPrimitive p (n₁ % p) - centredKernelPrimitive p (n₀ % p) := by
      have : (0 : ℝ) ≤ (p : ℝ) ^ 3 := by positivity
      linarith
    have hAL0 : (0 : ℝ) < (A : ℝ) + L := by linarith
    have hden : (A : ℝ) + L ≤ 2 * ((A : ℝ) + 1) := by linarith
    have hmain1 : (p : ℝ) ^ 3 / (7200 * ((A : ℝ) + 1)) ≤
        (centredKernelPrimitive p (n₁ % p) - centredKernelPrimitive p (n₀ % p)) / ((A : ℝ) + L) := by
      rw [div_le_div_iff₀ (by positivity) hAL0]
      nlinarith [pow_pos hpR 3]
    have herr : 3 / 2 * (p : ℝ) ^ 3 * L / ((A : ℝ) + 1) ^ 2 ≤
        (p : ℝ) ^ 3 / (33333 * ((A : ℝ) + 1)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos hpR 3, mul_pos (pow_pos hpR 3) (by linarith : (0 : ℝ) < (A : ℝ) + 1)]
    have hA0 : (0 : ℝ) < A := by linarith
    have hfin : (p : ℝ) ^ 3 / (14400 * A) ≤
        (p : ℝ) ^ 3 / (7200 * ((A : ℝ) + 1)) - (p : ℝ) ^ 3 / (33333 * ((A : ℝ) + 1)) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos hpR 3, mul_pos (pow_pos hpR 3) hA0,
        mul_pos (mul_pos (pow_pos hpR 3) hA0) hA0]
    have hΛ : (p : ℝ) ^ 3 / (14400 * A) ≤ kernelStatistic N (flatLargeRow A L) p := by linarith
    rw [le_div_iff₀ hpR]
    calc (p : ℝ) ^ 2 / (14400 * A) * p = (p : ℝ) ^ 3 / (14400 * A) := by ring
      _ ≤ kernelStatistic N (flatLargeRow A L) p := hΛ
      _ ≤ |kernelStatistic N (flatLargeRow A L) p| := le_abs_self _
  have := sum_le_sum hstat
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
