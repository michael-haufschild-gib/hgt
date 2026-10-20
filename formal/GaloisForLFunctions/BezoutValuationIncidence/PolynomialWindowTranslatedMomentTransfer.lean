import GaloisForLFunctions.BezoutValuationIncidence.PhaseUniformWindowSandwichAndQuadraticObservabilityHorizon
import GaloisForLFunctions.BiScaleUncertainty.CubicSievePhaseRecovery

/-!
# Polynomial-window transfer of every translated moment

A translated moment of degree `m` multiplies `m` shifted responses `s(k + h_i)`. Expanding the
product, it is a sum over moduli families `d : Fin m → [1, N]` of `∏ c(d_i)` times the number of
positions with `d_i ∣ k + h_i` for all `i`. By the Chinese remainder theorem that set is empty or a
single residue class modulo `lcm(d_i)`, so on every window of `K` consecutive positions its count
differs from `K / lcm(d_i)` by less than one. Hence, at every phase,

`|Σ_{A<k≤A+K} ∏_i s(k + h_i) - K T(h)| ≤ ‖c‖₁^m`,

where `T(h)` is the complete-period translated moment `translatedMoment N c h` used by the
arithmetic observation theory. With `‖c‖₁² ≤ S_N Q_Sel(c)` the error is at most
`(S_N Q_Sel(c))^{m/2}`; for centered moments `Q_Sel` is replaced by `(H - κ)² + V`.

So every observation that the complete-period recovery theorems use is available, to relative
accuracy `δ`, from one window of length `(S_N Q)^{m/2} / δ` at an arbitrary phase: polynomial
horizon in place of the period `N!`, with transfer constants independent of `N`. The window law
says nothing about windows shorter than this.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-! ## §1. Counting multiples on windows -/

private theorem card_Ioc_filter_dvd {x y : ℕ} (hxy : x ≤ y) (L : ℕ) :
    ((Ioc x y).filter (fun j => L ∣ j)).card = y / L - x / L := by
  have h1 := Nat.Ioc_filter_dvd_card_eq_div y L
  have h2 := Nat.Ioc_filter_dvd_card_eq_div x L
  have hsplit : (Ioc 0 y).filter (fun j => L ∣ j) =
      (Ioc 0 x).filter (fun j => L ∣ j) ∪ (Ioc x y).filter (fun j => L ∣ j) := by
    ext j
    simp only [mem_filter, mem_Ioc, mem_union]
    constructor
    · rintro ⟨⟨h0, hy⟩, hL⟩
      by_cases hjx : j ≤ x
      · exact Or.inl ⟨⟨h0, hjx⟩, hL⟩
      · exact Or.inr ⟨⟨by omega, hy⟩, hL⟩
    · rintro (⟨⟨h0, hx⟩, hL⟩ | ⟨⟨hx, hy⟩, hL⟩)
      · exact ⟨⟨h0, by omega⟩, hL⟩
      · exact ⟨⟨by omega, hy⟩, hL⟩
  have hdisj : Disjoint ((Ioc 0 x).filter (fun j => L ∣ j)) ((Ioc x y).filter (fun j => L ∣ j)) :=
    disjoint_left.mpr fun j hj1 hj2 => by
      simp only [mem_filter, mem_Ioc] at hj1 hj2
      omega
  rw [hsplit, card_union_of_disjoint hdisj] at h1
  omega

/-- Multiples of `L` among the shifted positions `k + s`, `A < k ≤ A + K`. -/
private theorem card_window_filter_dvd_add (A K L s : ℕ) :
    ((Icc (A + 1) (A + K)).filter (fun k => L ∣ k + s)).card =
      (A + K + s) / L - (A + s) / L := by
  rw [← card_Ioc_filter_dvd (by omega : A + s ≤ A + K + s) L]
  refine card_nbij' (fun k => k + s) (fun j => j - s) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [coe_filter, Set.mem_setOf_eq, mem_Icc, mem_Ioc] at hk ⊢
    exact ⟨⟨by omega, by omega⟩, hk.2⟩
  · intro j hj
    simp only [coe_filter, Set.mem_setOf_eq, mem_Icc, mem_Ioc] at hj ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.sub_add_cancel (by omega)]
    exact hj.2
  · intro k _
    simp
  · intro j hj
    simp only [coe_filter, Set.mem_setOf_eq, mem_Ioc] at hj
    simp only
    omega

/-- A difference of floors of `(x + K)/L` and `x/L` is within one of `K/L`. -/
private theorem abs_div_sub_div_sub_le (x K L : ℕ) (hL : 0 < L) :
    |(((x + K) / L - x / L : ℕ) : ℝ) - (K : ℝ) / L| ≤ 1 := by
  have hle : x / L ≤ (x + K) / L := Nat.div_le_div_right (by omega)
  rw [Nat.cast_sub hle]
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have e1 := Nat.div_add_mod (x + K) L
  have e2 := Nat.div_add_mod x L
  have m1 := Nat.mod_lt (x + K) hL
  have m2 := Nat.mod_lt x hL
  set q1 := (x + K) / L
  set q2 := x / L
  set r1 := (x + K) % L
  set r2 := x % L
  have e1R : (L : ℝ) * q1 + r1 = x + K := by exact_mod_cast e1
  have e2R : (L : ℝ) * q2 + r2 = x := by exact_mod_cast e2
  have m1R : (r1 : ℝ) < L := by exact_mod_cast m1
  have m2R : (r2 : ℝ) < L := by exact_mod_cast m2
  have r10 : (0 : ℝ) ≤ r1 := Nat.cast_nonneg _
  have r20 : (0 : ℝ) ≤ r2 := Nat.cast_nonneg _
  have hkey : ((q1 : ℝ) - q2 - K / L) * L = r2 - r1 := by
    field_simp
    linarith
  rw [abs_le]
  constructor
  · by_contra hlt
    push Not at hlt
    have : ((q1 : ℝ) - q2 - K / L) * L < -1 * L := mul_lt_mul_of_pos_right hlt hLR
    linarith
  · by_contra hlt
    push Not at hlt
    have : 1 * (L : ℝ) < ((q1 : ℝ) - q2 - K / L) * L := mul_lt_mul_of_pos_right hlt hLR
    linarith

/-- **Joint incidence on windows.** For moduli `d_i ∈ [1, N]` and lags `h_i`, the number of
positions in a window of length `K` with `d_i ∣ k + h_i` for all `i` is within one of `K/N!` times
its number on a complete factorial period. -/
theorem abs_card_joint_incidence_window_sub_le {N m : ℕ} (d h : Fin m → ℕ)
    (hd : ∀ i, d i ∈ Icc 1 N) (A K : ℕ) :
    |(((Icc (A + 1) (A + K)).filter (fun k => ∀ i, d i ∣ k + h i)).card : ℝ) -
        (K : ℝ) / N.factorial *
          (((Icc 1 N.factorial).filter (fun k => ∀ i, d i ∣ k + h i)).card : ℝ)| ≤ 1 := by
  classical
  set L := (univ : Finset (Fin m)).lcm d with hLdef
  have hdL : ∀ i, d i ∣ L := fun i => Finset.dvd_lcm (mem_univ i)
  have hLP : L ∣ N.factorial :=
    Finset.lcm_dvd fun i _ => Nat.dvd_factorial (mem_Icc.mp (hd i)).1 (mem_Icc.mp (hd i)).2
  have hL : 0 < L := Nat.pos_of_dvd_of_pos hLP (Nat.factorial_pos N)
  have hP : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  by_cases hS : ∃ n0, ∀ i, d i ∣ n0 + h i
  · obtain ⟨n0, hn0⟩ := hS
    set s := L - n0 % L with hsdef
    have hLs : L ∣ n0 + s := by
      have h1 := Nat.div_add_mod n0 L
      have h2 := Nat.mod_lt n0 hL
      refine ⟨n0 / L + 1, ?_⟩
      rw [hsdef, Nat.mul_succ]
      omega
    -- the joint incidence set is the residue class `-s` modulo `L`
    have hiff : ∀ n, (∀ i, d i ∣ n + h i) ↔ L ∣ n + s := by
      intro n
      constructor
      · intro hn
        refine Finset.lcm_dvd fun i _ => ?_
        have a1 : ((d i : ℕ) : ℤ) ∣ (n : ℤ) + h i := by exact_mod_cast hn i
        have a2 : ((d i : ℕ) : ℤ) ∣ (n0 : ℤ) + h i := by exact_mod_cast hn0 i
        have a3 : ((d i : ℕ) : ℤ) ∣ (n0 : ℤ) + s := by exact_mod_cast (hdL i).trans hLs
        have : ((d i : ℕ) : ℤ) ∣ (n : ℤ) + s := by
          have := dvd_add (dvd_sub a1 a2) a3
          rwa [show (n : ℤ) + h i - (n0 + h i) + (n0 + s) = n + s by ring] at this
        exact_mod_cast this
      · intro hn i
        have a1 : ((d i : ℕ) : ℤ) ∣ (n : ℤ) + s := by exact_mod_cast (hdL i).trans hn
        have a3 : ((d i : ℕ) : ℤ) ∣ (n0 : ℤ) + s := by exact_mod_cast (hdL i).trans hLs
        have a4 : ((d i : ℕ) : ℤ) ∣ (n0 : ℤ) + h i := by exact_mod_cast hn0 i
        have := dvd_add (dvd_sub a1 a3) a4
        rw [show (n : ℤ) + s - (n0 + s) + (n0 + h i) = n + h i by ring] at this
        exact_mod_cast this
    have hW : (Icc (A + 1) (A + K)).filter (fun k => ∀ i, d i ∣ k + h i) =
        (Icc (A + 1) (A + K)).filter (fun k => L ∣ k + s) := filter_congr fun k _ => hiff k
    have hPer : (Icc 1 N.factorial).filter (fun k => ∀ i, d i ∣ k + h i) =
        (Icc (0 + 1) (0 + N.factorial)).filter (fun k => L ∣ k + s) := by
      simp only [zero_add]
      exact filter_congr fun k _ => hiff k
    rw [hW, hPer, card_window_filter_dvd_add, card_window_filter_dvd_add]
    have hcount : (0 + N.factorial + s) / L - (0 + s) / L = N.factorial / L := by
      rw [zero_add, zero_add, Nat.add_div_of_dvd_right hLP, Nat.add_sub_cancel]
    rw [hcount, Nat.cast_div hLP (by exact_mod_cast hL.ne')]
    have : (K : ℝ) / N.factorial * ((N.factorial : ℝ) / L) = (K : ℝ) / L := by
      field_simp
    rw [this, show A + K + s = (A + s) + K by omega]
    exact abs_div_sub_div_sub_le (A + s) K L hL
  · push Not at hS
    have h0 : ∀ t : Finset ℕ, (t.filter (fun k => ∀ i, d i ∣ k + h i)) = ∅ :=
      fun t => filter_eq_empty_iff.mpr fun k _ hk => by
        obtain ⟨i, hi⟩ := hS k
        exact hi (hk i)
    rw [h0, h0]
    simp

/-! ## §2. Expansion of translated products -/

/-- A product of shifted responses expands over moduli families with a joint incidence factor. -/
theorem prod_sieveSeq_shift_eq_sum {N m : ℕ} (c : ℕ → ℝ) (h : Fin m → ℕ) (k : ℕ) :
    (∏ i, sieveSeq N c (k + h i)) =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 N),
        (∏ i, c (p i)) * (if ∀ i, p i ∣ k + h i then 1 else 0) := by
  classical
  unfold sieveSeq
  simp_rw [sum_filter]
  rw [prod_univ_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [prod_ite_zero]
  simp only [mem_univ, true_implies]
  split_ifs <;> simp

private theorem sum_window_prod_eq {N m : ℕ} (c : ℕ → ℝ) (h : Fin m → ℕ) (t : Finset ℕ) :
    (∑ k ∈ t, ∏ i, sieveSeq N c (k + h i)) =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 N),
        (∏ i, c (p i)) * ((t.filter (fun k => ∀ i, p i ∣ k + h i)).card : ℝ) := by
  classical
  simp_rw [prod_sieveSeq_shift_eq_sum c h]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [← mul_sum, sum_boole]

/-- The translated product is periodic modulo `N!`, so its complete-period average may be taken
over `[1, N!]`. -/
theorem translatedMoment_eq_Icc (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (h : Fin m → ℕ) :
    SieveMoments.translatedMoment N c h =
      (∑ k ∈ Icc 1 N.factorial, ∏ i, sieveSeq N c (k + h i)) / (N.factorial : ℝ) := by
  unfold SieveMoments.translatedMoment
  congr 1
  have hper : ∀ x : ℕ, sieveSeq N c (N.factorial + x) = sieveSeq N c x := fun x => by
    unfold sieveSeq
    refine sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨hd, hdx⟩
      exact ⟨hd, (Nat.dvd_add_right (Nat.dvd_factorial hd.1 hd.2)).mp hdx⟩
    · rintro ⟨hd, hdx⟩
      exact ⟨hd, (Nat.dvd_add_right (Nat.dvd_factorial hd.1 hd.2)).mpr hdx⟩
  obtain ⟨P, hP⟩ : ∃ P, N.factorial = P + 1 := ⟨N.factorial - 1, by
    have := Nat.factorial_pos N; omega⟩
  rw [hP, sum_range_succ', Finset.sum_Icc_succ_top (by omega)]
  have hshift : (∑ k ∈ range P, ∏ i, sieveSeq N c (k + 1 + h i)) =
      ∑ k ∈ Icc 1 P, ∏ i, sieveSeq N c (k + h i) := by
    have hset : Icc 1 P = (Ico 0 P).map (addRightEmbedding 1) := by
      rw [Finset.map_add_right_Ico]
      ext x
      simp only [mem_Icc, mem_Ico]
      omega
    rw [range_eq_Ico, hset, sum_map]
    rfl
  rw [hshift]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  rw [← hP, zero_add, hper]

/-! ## §3. The transfer law -/

/-- **Window transfer of translated moments.** At every phase, the window sum of a degree-`m`
translated product differs from `K` times its complete-period average by at most `‖c‖₁^m`. -/
theorem abs_window_translatedMoment_sub_le (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (h : Fin m → ℕ)
    (A K : ℕ) :
    |(∑ k ∈ Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + h i)) -
        (K : ℝ) * SieveMoments.translatedMoment N c h| ≤ (∑ d ∈ Icc 1 N, |c d|) ^ m := by
  classical
  rw [translatedMoment_eq_Icc, sum_window_prod_eq, sum_window_prod_eq]
  have hrw : (K : ℝ) * ((∑ p ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 N),
        (∏ i, c (p i)) * (((Icc 1 N.factorial).filter
          (fun k => ∀ i, p i ∣ k + h i)).card : ℝ)) / (N.factorial : ℝ)) =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 N),
        (∏ i, c (p i)) * ((K : ℝ) / N.factorial *
          (((Icc 1 N.factorial).filter (fun k => ∀ i, p i ∣ k + h i)).card : ℝ)) := by
    rw [mul_div_assoc', mul_sum, sum_div]
    exact sum_congr rfl fun p _ => by ring
  rw [hrw, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hpt : ∀ p ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 N),
      |(∏ i, c (p i)) * (((Icc (A + 1) (A + K)).filter (fun k => ∀ i, p i ∣ k + h i)).card : ℝ) -
        (∏ i, c (p i)) * ((K : ℝ) / N.factorial *
          (((Icc 1 N.factorial).filter (fun k => ∀ i, p i ∣ k + h i)).card : ℝ))| ≤
        ∏ i, |c (p i)| := by
    intro p hp
    rw [← mul_sub, abs_mul, Finset.abs_prod]
    exact mul_le_of_le_one_right (prod_nonneg fun _ _ => abs_nonneg _)
      (abs_card_joint_incidence_window_sub_le p h (Fintype.mem_piFinset.mp hp) A K)
  refine (sum_le_sum hpt).trans_eq ?_
  rw [← prod_univ_sum (fun _ : Fin m => Icc 1 N) (fun _ d => |c d|), prod_const, card_univ,
    Fintype.card_fin]

/-- **Relative transfer.** The error is at most `(√(S_N Q_Sel(c)))^m`. -/
theorem abs_window_translatedMoment_sub_le_observabilityConstant (N : ℕ) (c : ℕ → ℝ)
    {m : ℕ} (h : Fin m → ℕ) (A K : ℕ) :
    |(∑ k ∈ Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + h i)) -
        (K : ℝ) * SieveMoments.translatedMoment N c h| ≤
      Real.sqrt (sieveWindowObservabilityConstant N * selbergTotientDiagonalForm N c) ^ m := by
  refine (abs_window_translatedMoment_sub_le N c h A K).trans
    (pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) ?_ m)
  exact Real.le_sqrt_of_sq_le (sum_abs_sq_le_observabilityConstant_mul_selberg N c)

/-- **Centered relative transfer.** For centered responses `s - κ` the period scale is
`(H - κ)² + V`; with `κ = H` the error of a degree-`m` moment is at most `(S_N V)^{m/2}`. -/
theorem abs_window_centeredTranslatedMoment_sub_le {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (κ : ℝ)
    {m : ℕ} (h : Fin m → ℕ) (A K : ℕ) :
    |(∑ k ∈ Icc (A + 1) (A + K), ∏ i, (sieveSeq N c (k + h i) - κ)) -
        (K : ℝ) * SieveMoments.translatedMoment N (sieveRowShift c κ) h| ≤
      Real.sqrt (sieveWindowObservabilityConstant N *
        ((finiteHarmonicSum N c - κ) ^ 2 + sieveVariance N c)) ^ m := by
  have h1 := abs_window_translatedMoment_sub_le_observabilityConstant N (sieveRowShift c κ) h A K
  rw [selbergTotientDiagonalForm_sieveRowShift hN] at h1
  simpa only [sieveSeq_sieveRowShift hN] using h1

/-- The window law in the cyclic language of the observation theory: the window sum is within
`‖c‖₁^m` of `K` times the cyclic translation moment of the residue signal on `ZMod N!`. -/
theorem norm_window_translationMoment_sub_le (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (h : Fin m → ℕ)
    (A K : ℕ) :
    ‖(((∑ k ∈ Icc (A + 1) (A + K), ∏ i, sieveSeq N c (k + h i) : ℝ)) : ℂ) -
        (K : ℂ) * SieveMoments.translationMoment (AffineSieve.residueSignal N (fun d => (c d : ℂ)))
          (fun i => (h i : ZMod N.factorial))‖ ≤ (∑ d ∈ Icc 1 N, |c d|) ^ m := by
  rw [← SieveMoments.translatedMoment_complex_eq,
    show (K : ℂ) = ((K : ℝ) : ℂ) from rfl, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_window_translatedMoment_sub_le N c h A K

end

end GaloisForLFunctions.BezoutValuationIncidence
