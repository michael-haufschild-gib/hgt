import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSumDiscreteFourthMoment
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardEnergyLargeGcdAlgebra
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardRatioSeparation
import GaloisForLFunctions.RHTower.ShortWindowNoGo

set_option autoImplicit false

/-!
# Guth–Maynard Lemma 11.9: the large-gcd part of the discrete third moment

For `T ≥ 2`, `T^{3/4} ≤ N ≤ T`, `D = N²/T` and every `1`-separated `W ⊆ [T₀, T₀ + T]`
(Guth–Maynard, arXiv 2405.20552, Lemma 11.9), unconditionally:

`Σ_{n₁,n₂ ∼ N, gcd(n₁,n₂) ≥ D} |R(n₁/n₂)|³ ⪅ N|W|³ + N T^{1/4} |W|^{21/8} + E(W)^{1/2} |W|^{1/2} N²`.

Proof. A pair with `gcd = d ≥ D` is `(d a, d b)` with `a, b ∈ S_d = {a : N < da ≤ 2N}`, and `R(n₁/n₂) =
R(a/b)` (`sum_dvd_pairs_eq`). For `d > N`, `S_d ⊆ {1}` and the contribution is `≤ N|W|³`. For
`D ≤ d ≤ N`, `S_d ⊆ (M, 2M+1]` with `M = ⌊N/d⌋ ≤ T/N ≤ T^{1/4}`, so the unconditional short-block
forms of Lemmas 11.5 and 11.6 apply; Cauchy–Schwarz in `(a, b)` and then in `d`
(`Real.sum_sqrt_mul_sqrt_le`), `Σ_{d ≥ D} d^{−2} ≤ 2/D` and `Σ_{d ≤ N} d^{−1} ≤ 1 + log N`
(corpus) give the bound
`(|W|²N + |W|T + |W|^{5/4}T^{1/2}N)^{1/2}(N|W|⁴ + ET + E^{3/4}|W|T^{1/2}N)^{1/2}` up to `T^{o(1)}`,
and the exponent algebra `largeGcd_algebra_rpow` finishes.
-/

open MeasureTheory Set Finset

namespace RHTower.GuthMaynard

noncomputable section

/-! ### Extracting the common factor -/

/-- `S_d = {a : N < d a ≤ 2N}`, as the quotients by `d` of the multiples of `d` in `(N, 2N]`. -/
def multiplesBlock (N d : ℕ) : Finset ℕ :=
  ((Finset.Ioc N (2 * N)).filter fun n => d ∣ n).image fun n => n / d

/-- **Extracting `d`.** For `d ≥ 1` and any `G`:
`Σ_{(n₁,n₂) ∈ (N,2N]², d | n₁, d | n₂} G(n₁/n₂) = Σ_{a,b ∈ S_d} G(a/b)`. -/
theorem sum_dvd_pairs_eq (N : ℕ) {d : ℕ} (hd : 1 ≤ d) (G : ℝ → ℝ) :
    ∑ p ∈ (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter (fun p => d ∣ p.1 ∧ d ∣ p.2),
        G ((p.1 : ℝ) / p.2) =
      ∑ a ∈ multiplesBlock N d, ∑ b ∈ multiplesBlock N d, G ((a : ℝ) / b) := by
  classical
  set A := (Finset.Ioc N (2 * N)).filter fun n => d ∣ n
  have hprod : (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
      (fun p => d ∣ p.1 ∧ d ∣ p.2) = A ×ˢ A := by
    ext p
    simp only [A, mem_filter, mem_product]
    tauto
  have hinj : Set.InjOn (fun n => n / d) A := by
    intro n hn m hm h
    have hn' := (mem_filter.mp hn).2
    have hm' := (mem_filter.mp hm).2
    have h' : n / d = m / d := h
    calc n = n / d * d := (Nat.div_mul_cancel hn').symm
      _ = m / d * d := by rw [h']
      _ = m := Nat.div_mul_cancel hm'
  have hd0 : (d : ℝ) ≠ 0 := by have : (0 : ℝ) < d := by exact_mod_cast hd; exact this.ne'
  have hratio : ∀ n ∈ A, ∀ m ∈ A, (((n / d : ℕ) : ℝ) / ((m / d : ℕ) : ℝ)) = (n : ℝ) / m := by
    intro n hn m hm
    rw [Nat.cast_div (mem_filter.mp hn).2 hd0, Nat.cast_div (mem_filter.mp hm).2 hd0]
    field_simp
  rw [hprod, sum_product]
  unfold multiplesBlock
  rw [sum_image hinj]
  refine sum_congr rfl fun n hn => ?_
  rw [sum_image hinj]
  refine sum_congr rfl fun m hm => ?_
  rw [hratio n hn m hm]

/-- For `1 ≤ d ≤ N`: `S_d ⊆ (M, 2M+1]` with `M = ⌊N/d⌋ ≥ 1`. -/
theorem multiplesBlock_subset {N d : ℕ} (hd : 1 ≤ d) :
    multiplesBlock N d ⊆ Finset.Ioc (N / d) (2 * (N / d) + 1) := by
  intro a ha
  obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
  obtain ⟨hnI, hdn⟩ := mem_filter.mp hn
  obtain ⟨h1, h2⟩ := mem_Ioc.mp hnI
  obtain ⟨k, rfl⟩ := hdn
  have hd0 : 0 < d := hd
  rw [Nat.mul_div_cancel_left _ hd0]
  have hdiv := Nat.div_add_mod N d
  have hmod := Nat.mod_lt N hd0
  refine mem_Ioc.mpr ⟨?_, ?_⟩
  · by_contra hc
    have : k ≤ N / d := by omega
    have : d * k ≤ d * (N / d) := Nat.mul_le_mul_left d this
    omega
  · by_contra hc
    have : 2 * (N / d) + 2 ≤ k := by omega
    have h3 : d * (2 * (N / d) + 2) ≤ d * k := Nat.mul_le_mul_left d this
    have e : d * (2 * (N / d) + 2) = 2 * (d * (N / d)) + 2 * d := by ring
    omega

/-- For `d > N`: `S_d ⊆ {1}`. -/
theorem multiplesBlock_subset_one {N d : ℕ} (hd : N < d) : multiplesBlock N d ⊆ {1} := by
  intro a ha
  obtain ⟨n, hn, rfl⟩ := mem_image.mp ha
  obtain ⟨hnI, hdn⟩ := mem_filter.mp hn
  obtain ⟨h1, h2⟩ := mem_Ioc.mp hnI
  obtain ⟨k, rfl⟩ := hdn
  have hd0 : 0 < d := by omega
  rw [Nat.mul_div_cancel_left _ hd0, mem_singleton]
  rcases Nat.lt_or_ge k 2 with hk | hk
  · rcases Nat.lt_or_ge k 1 with hk1 | hk1
    · have : k = 0 := by omega
      subst this; omega
    · omega
  · have : d * 2 ≤ d * k := Nat.mul_le_mul_left d hk
    omega

/-- **Regrouping by the gcd.** For `D > 0` and `F ≥ 0`:
`Σ_{p : gcd p ≥ D} F(p) ≤ Σ_{⌈D⌉ ≤ d ≤ 2N} Σ_{p : d | p₁, d | p₂} F(p)`. -/
theorem sum_largeGcd_le (N : ℕ) {D : ℝ} (hD : 0 < D) {F : ℕ × ℕ → ℝ} (hF : ∀ p, 0 ≤ F p) :
    ∑ p ∈ (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
        (fun p => D ≤ ((Nat.gcd p.1 p.2 : ℕ) : ℝ)), F p ≤
      ∑ d ∈ Finset.Icc ⌈D⌉₊ (2 * N), ∑ p ∈ (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
        (fun p => d ∣ p.1 ∧ d ∣ p.2), F p := by
  classical
  set P := Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)
  have hmaps : ∀ p ∈ P.filter (fun p => D ≤ ((Nat.gcd p.1 p.2 : ℕ) : ℝ)),
      Nat.gcd p.1 p.2 ∈ Finset.Icc ⌈D⌉₊ (2 * N) := by
    intro p hp
    obtain ⟨hpP, hpD⟩ := mem_filter.mp hp
    obtain ⟨hp1, -⟩ := mem_product.mp hpP
    have h1 := mem_Ioc.mp hp1
    refine mem_Icc.mpr ⟨Nat.ceil_le.mpr hpD, ?_⟩
    exact (Nat.gcd_le_left _ (by omega)).trans h1.2
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_le_sum fun d _ => ?_
  refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => hF p
  intro p hp
  simp only [mem_filter] at hp ⊢
  obtain ⟨⟨hpP, -⟩, hpd⟩ := hp
  refine ⟨hpP, ?_, ?_⟩
  · rw [← hpd]; exact Nat.gcd_dvd_left _ _
  · rw [← hpd]; exact Nat.gcd_dvd_right _ _

/-! ### The per-`d` Cauchy–Schwarz -/

/-- `Σ_{a,b ∈ S} |R(a/b)|³ ≤ (Σ |R|²)^{1/2} (Σ |R|⁴)^{1/2}` (`Real.sum_sqrt_mul_sqrt_le`). -/
theorem sum_cube_le_sqrt_mul_sqrt (W : Finset ℝ) (S : Finset ℕ) :
    ∑ a ∈ S, ∑ b ∈ S, ‖lagSum W ((a : ℝ) / b)‖ ^ 3 ≤
      Real.sqrt (∑ a ∈ S, ∑ b ∈ S, ‖lagSum W ((a : ℝ) / b)‖ ^ 2) *
        Real.sqrt (∑ a ∈ S, ∑ b ∈ S, ‖lagSum W ((a : ℝ) / b)‖ ^ 4) := by
  have h := Real.sum_sqrt_mul_sqrt_le (S ×ˢ S)
    (f := fun q : ℕ × ℕ => ‖lagSum W ((q.1 : ℝ) / q.2)‖ ^ 2)
    (g := fun q : ℕ × ℕ => ‖lagSum W ((q.1 : ℝ) / q.2)‖ ^ 4) (fun _ => by positivity)
    (fun _ => by positivity)
  simp only [sum_product] at h
  refine le_trans (le_of_eq ?_) h
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  have h0 := norm_nonneg (lagSum W ((a : ℝ) / b))
  have e1 : Real.sqrt (‖lagSum W ((a : ℝ) / b)‖ ^ 2) = ‖lagSum W ((a : ℝ) / b)‖ :=
    Real.sqrt_sq h0
  have e2 : Real.sqrt (‖lagSum W ((a : ℝ) / b)‖ ^ 4) = ‖lagSum W ((a : ℝ) / b)‖ ^ 2 := by
    rw [show ‖lagSum W ((a : ℝ) / b)‖ ^ 4 = (‖lagSum W ((a : ℝ) / b)‖ ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [e1, e2]
  ring

/-! ### Sums over the gcd -/

/-- For gcds `D ≤ d ≤ N` (`D > 0`, `N ≥ 1`):
`Σ_d (α (N/d) + β (N/d)²) ≤ α N (1 + log N) + β N² (2/D)` for `α, β ≥ 0`. -/
theorem sum_linear_quadratic_le {N : ℕ} (hN : 1 ≤ N) {D α β : ℝ} (hD : 0 < D) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) {I : Finset ℕ} (hI : ∀ d ∈ I, 1 ≤ d ∧ D ≤ d ∧ d ≤ N) :
    ∑ d ∈ I, (α * ((N : ℝ) / d) + β * ((N : ℝ) / d) ^ 2) ≤
      α * N * (1 + Real.log N) + β * (N : ℝ) ^ 2 * (2 / D) := by
  have hsub : I ⊆ Finset.Icc 1 N := fun d hd => mem_Icc.mpr ⟨(hI d hd).1, (hI d hd).2.2⟩
  have hH : ∑ d ∈ I, (1 : ℝ) / d ≤ 1 + Real.log N :=
    (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
      (harmonic_Icc_le_one_add_log N hN)
  have hQ : ∑ d ∈ I, 1 / (d : ℝ) ^ 2 ≤ 2 / D :=
    GaloisForLFunctions.ArithmeticPositivityTheory.sum_one_div_sq_le_two_div I hD
      fun d hd => (hI d hd).2.1
  have e : ∑ d ∈ I, (α * ((N : ℝ) / d) + β * ((N : ℝ) / d) ^ 2) =
      α * N * ∑ d ∈ I, (1 : ℝ) / d + β * (N : ℝ) ^ 2 * ∑ d ∈ I, 1 / (d : ℝ) ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    ring
  rw [e]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  gcongr

/-! ### Lemma 11.9 -/

/-- **Guth–Maynard Lemma 11.9**, unconditionally: for every `ε > 0` there is `C ≥ 0` such that for
`T ≥ 2`, `T^{3/4} ≤ N ≤ T` and every `1`-separated `W ⊆ [T₀, T₀ + T]`:
`Σ_{n₁,n₂ ∈ (N,2N], gcd(n₁,n₂) ≥ N²/T} |R(n₁/n₂)|³ ≤
  C T^ε (N|W|³ + N T^{1/4}|W|^{21/8} + E(W)^{1/2}|W|^{1/2}N²)`. -/
theorem guthMaynard_lemma119 {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ (N : ℕ) (W : Finset ℝ) (T T₀ : ℝ), 2 ≤ T → T ^ (3 / 4 : ℝ) ≤ N →
      (N : ℝ) ≤ T → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) → IsSeparated 1 W →
      ∑ p ∈ (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
          (fun p => (N : ℝ) ^ 2 / T ≤ ((Nat.gcd p.1 p.2 : ℕ) : ℝ)),
          ‖lagSum W ((p.1 : ℝ) / p.2)‖ ^ 3 ≤
        C * T ^ ε * (N * (W.card : ℝ) ^ 3 + N * T ^ (1 / 4 : ℝ) * (W.card : ℝ) ^ (21 / 8 : ℝ) +
          Real.sqrt (additiveEnergy W) * Real.sqrt W.card * (N : ℝ) ^ 2) := by
  classical
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = ε / 2 := ⟨_, rfl⟩
  have hε₀0 : 0 < ε₀ := by rw [hε₀]; positivity
  obtain ⟨C₂, hC₂, h115⟩ := guthMaynard_lemma115_short hε₀0
  obtain ⟨C₄, hC₄, h116⟩ := guthMaynard_lemma116_short hε₀0
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 6 * Real.sqrt (C₂ * C₄) * (3 + 1 / ε₀) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨K + 1, by positivity, fun N W T T₀ hT hNT hNle hW hsep => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hTε₀ : 1 ≤ T ^ ε₀ := Real.one_le_rpow hT1 hε₀0.le
  have hTε : T ^ ε = T ^ ε₀ * T ^ ε₀ := by
    rw [← Real.rpow_add hT0, hε₀]; ring_nf
  have hT34 : 1 ≤ T ^ (3 / 4 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := hT34.trans hNT
    exact_mod_cast this
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set X : ℝ := (W.card : ℝ) with hXdef
  set E : ℝ := (additiveEnergy W : ℝ) with hEdef
  set target : ℝ := N * X ^ 3 + N * T ^ (1 / 4 : ℝ) * X ^ (21 / 8 : ℝ) +
    Real.sqrt E * Real.sqrt X * (N : ℝ) ^ 2 with htarget
  have htarget0 : 0 ≤ target := by positivity
  -- the empty set
  rcases W.eq_empty_or_nonempty with hW0 | hWne
  · have hz : ∀ v, lagSum W v = 0 := fun v => by simp [lagSum, hW0]
    simp only [hz, norm_zero]
    rw [sum_const_zero]
    norm_num
    positivity
  have hX1 : 1 ≤ X := by
    have : 1 ≤ W.card := card_pos.mpr hWne
    exact_mod_cast this
  have hXE : X ^ 2 ≤ E := card_sq_le_additiveEnergy W
  have hE3 : E ≤ 3 * X ^ 3 := additiveEnergy_le_three_mul_card_pow hsep
  have hXT : X ≤ 2 * T := by
    have := card_le_of_separated_subset_Icc hT0.le hW hsep
    linarith
  set D : ℝ := (N : ℝ) ^ 2 / T with hDdef
  have hD0 : 0 < D := by positivity
  have hNTD : (N : ℝ) / D = T / N := by rw [hDdef]; field_simp
  have hTN : T / N ≤ T ^ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    calc T = T ^ (1 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by
          rw [← Real.rpow_add hT0]; norm_num
      _ ≤ T ^ (1 / 4 : ℝ) * N := mul_le_mul_of_nonneg_left hNT (by positivity)
  set F : ℕ × ℕ → ℝ := fun p => ‖lagSum W ((p.1 : ℝ) / p.2)‖ ^ 3
  set G : ℕ → ℝ := fun d => ∑ a ∈ multiplesBlock N d, ∑ b ∈ multiplesBlock N d,
    ‖lagSum W ((a : ℝ) / b)‖ ^ 3
  set I := Finset.Icc ⌈D⌉₊ (2 * N)
  have hI1 : ∀ d ∈ I, 1 ≤ d := fun d hd =>
    le_trans (Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hD0).ne') (mem_Icc.mp hd).1
  -- regroup by the gcd and extract it
  have hreg : ∑ p ∈ (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
      (fun p => D ≤ ((Nat.gcd p.1 p.2 : ℕ) : ℝ)), F p ≤ ∑ d ∈ I, G d := by
    refine (sum_largeGcd_le N hD0 (F := F) fun p => by positivity).trans (le_of_eq ?_)
    refine sum_congr rfl fun d hd => ?_
    exact sum_dvd_pairs_eq N (hI1 d hd) (fun v => ‖lagSum W v‖ ^ 3)
  -- the large gcds `d > N`
  have hlarge : ∑ d ∈ I.filter (fun d => ¬ d ≤ N), G d ≤ N * X ^ 3 := by
    have hG : ∀ d ∈ I.filter (fun d => ¬ d ≤ N), G d ≤ X ^ 3 := by
      intro d hd
      have hdN : N < d := by have := (mem_filter.mp hd).2; omega
      have hsub := multiplesBlock_subset_one (N := N) hdN
      have h1 : G d ≤ ∑ a ∈ ({1} : Finset ℕ), ∑ b ∈ ({1} : Finset ℕ),
          ‖lagSum W ((a : ℝ) / b)‖ ^ 3 := by
        simp only [G]
        rw [← sum_product', ← sum_product']
        exact sum_le_sum_of_subset_of_nonneg (product_subset_product hsub hsub)
          fun _ _ _ => by positivity
      simpa [lagSum_one] using h1
    have hcard : ((I.filter fun d => ¬ d ≤ N).card : ℝ) ≤ N := by
      have : (I.filter fun d => ¬ d ≤ N) ⊆ Finset.Ioc N (2 * N) := fun d hd => by
        obtain ⟨hdI, hdN⟩ := mem_filter.mp hd
        exact mem_Ioc.mpr ⟨by omega, (mem_Icc.mp hdI).2⟩
      have h := card_le_card this
      rw [Nat.card_Ioc, show 2 * N - N = N by omega] at h
      exact_mod_cast h
    calc ∑ d ∈ I.filter (fun d => ¬ d ≤ N), G d ≤ ∑ _d ∈ I.filter (fun d => ¬ d ≤ N), X ^ 3 :=
          sum_le_sum hG
      _ = ((I.filter fun d => ¬ d ≤ N).card : ℝ) * X ^ 3 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ N * X ^ 3 := mul_le_mul_of_nonneg_right hcard (by positivity)
  -- the small gcds `D ≤ d ≤ N`: Lemmas 11.5 and 11.6 at `M = ⌊N/d⌋ ≤ T^{1/4}`
  set Is := I.filter (fun d => d ≤ N)
  have hIs : ∀ d ∈ Is, 1 ≤ d ∧ D ≤ d ∧ d ≤ N := fun d hd => by
    obtain ⟨hdI, hdN⟩ := mem_filter.mp hd
    exact ⟨hI1 d hdI, (Nat.ceil_le.mp (mem_Icc.mp hdI).1), hdN⟩
  have hM : ∀ d ∈ Is, 1 ≤ N / d ∧ ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d ∧
      (N : ℝ) / d ≤ T ^ (1 / 4 : ℝ) := by
    intro d hd
    obtain ⟨hd1, hdD, hdN⟩ := hIs d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    refine ⟨(Nat.one_le_div_iff hd1).mpr hdN, Nat.cast_div_le, ?_⟩
    calc (N : ℝ) / d ≤ (N : ℝ) / D := div_le_div_of_nonneg_left (by positivity) hD0 hdD
      _ = T / N := hNTD
      _ ≤ T ^ (1 / 4 : ℝ) := hTN
  set A : ℕ → ℝ := fun d => ∑ a ∈ multiplesBlock N d, ∑ b ∈ multiplesBlock N d,
    ‖lagSum W ((a : ℝ) / b)‖ ^ 2
  set B : ℕ → ℝ := fun d => ∑ a ∈ multiplesBlock N d, ∑ b ∈ multiplesBlock N d,
    ‖lagSum W ((a : ℝ) / b)‖ ^ 4
  have hA : ∀ d ∈ Is, A d ≤ C₂ * T ^ ε₀ * ((X ^ 2 + X ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) *
      ((N : ℝ) / d) + X * ((N : ℝ) / d) ^ 2) := by
    intro d hd
    obtain ⟨hM1, hMle, hMT⟩ := hM d hd
    have h := h115 W (N / d) (multiplesBlock N d) T T₀ hT hM1 (hMle.trans hMT)
      (multiplesBlock_subset (hIs d hd).1) hW hsep
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine (heathBrownMajorant_mono (Nat.cast_nonneg _) (Nat.cast_nonneg _) hMle hT0.le).trans
      (le_of_eq ?_)
    unfold heathBrownMajorant; ring
  have hB : ∀ d ∈ Is, B d ≤ C₄ * T ^ ε₀ * ((X ^ 4 + E ^ (3 / 4 : ℝ) * X * T ^ (1 / 2 : ℝ)) *
      ((N : ℝ) / d) + E * ((N : ℝ) / d) ^ 2) := by
    intro d hd
    obtain ⟨hM1, hMle, hMT⟩ := hM d hd
    have h := h116 W (N / d) (multiplesBlock N d) T T₀ hT hM1 (hMle.trans hMT)
      (multiplesBlock_subset (hIs d hd).1) hW hsep
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hM0 : (0 : ℝ) ≤ ((N / d : ℕ) : ℝ) := Nat.cast_nonneg _
    have hsq := pow_le_pow_left₀ hM0 hMle 2
    have h1 : 0 ≤ X ^ 4 := by positivity
    have h2 : 0 ≤ E ^ (3 / 4 : ℝ) * X * T ^ (1 / 2 : ℝ) := by positivity
    have hE0 : 0 ≤ E := by positivity
    calc X ^ 4 * ((N / d : ℕ) : ℝ) + ((N / d : ℕ) : ℝ) ^ 2 * additiveEnergy W +
          E ^ (3 / 4 : ℝ) * X * T ^ (1 / 2 : ℝ) * ((N / d : ℕ) : ℝ)
        = (X ^ 4 + E ^ (3 / 4 : ℝ) * X * T ^ (1 / 2 : ℝ)) * ((N / d : ℕ) : ℝ) +
            E * ((N / d : ℕ) : ℝ) ^ 2 := by ring
      _ ≤ _ := by gcongr
  have hGs : ∀ d ∈ Is, G d ≤ Real.sqrt (A d) * Real.sqrt (B d) := fun d _ =>
    sum_cube_le_sqrt_mul_sqrt W (multiplesBlock N d)
  set L : ℝ := 1 + Real.log N
  have hL0 : 0 ≤ L := by have := Real.log_nonneg hNr; linarith
  have hLT : L + 2 ≤ (3 + 1 / ε₀) * T ^ ε₀ := by
    have h1 : Real.log N ≤ Real.log T := Real.log_le_log (by linarith) hNle
    have h2 : Real.log T ≤ T ^ ε₀ / ε₀ := Real.log_le_rpow_div hT0.le hε₀0
    have h3 : T ^ ε₀ / ε₀ = (1 / ε₀) * T ^ ε₀ := by ring
    nlinarith
  set a : ℝ := X ^ 2 * N + X * T + X ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N
  set b : ℝ := X ^ 4 * N + E * T + E ^ (3 / 4 : ℝ) * X * T ^ (1 / 2 : ℝ) * N
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hsumA : ∑ d ∈ Is, A d ≤ C₂ * T ^ ε₀ * ((L + 2) * a) := by
    refine (sum_le_sum hA).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (sum_linear_quadratic_le hN1 hD0 (by positivity) (by positivity) hIs).trans ?_
    have e : X * (N : ℝ) ^ 2 * (2 / D) = 2 * (X * T) := by rw [hDdef]; field_simp
    rw [e]
    have : 0 ≤ X * T := by positivity
    have : 0 ≤ (X ^ 2 + X ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) * N := by positivity
    simp only [a]
    nlinarith
  have hsumB : ∑ d ∈ Is, B d ≤ C₄ * T ^ ε₀ * ((L + 2) * b) := by
    refine (sum_le_sum hB).trans ?_
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (sum_linear_quadratic_le hN1 hD0 (by positivity) (by positivity) hIs).trans ?_
    have e : E * (N : ℝ) ^ 2 * (2 / D) = 2 * (E * T) := by rw [hDdef]; field_simp
    rw [e]
    have : 0 ≤ E * T := by positivity
    have : 0 ≤ (X ^ 4 + E ^ (3 / 4 : ℝ) * X * T ^ (1 / 2 : ℝ)) * N := by positivity
    simp only [b]
    nlinarith
  have halg := largeGcd_algebra_rpow hX1 hT1 hXE hE3 hXT hNT
  have hsmall : ∑ d ∈ Is, G d ≤ K * T ^ ε * target := by
    calc ∑ d ∈ Is, G d ≤ ∑ d ∈ Is, Real.sqrt (A d) * Real.sqrt (B d) := sum_le_sum hGs
      _ ≤ Real.sqrt (∑ d ∈ Is, A d) * Real.sqrt (∑ d ∈ Is, B d) :=
          Real.sum_sqrt_mul_sqrt_le Is (fun d => by positivity) (fun d => by positivity)
      _ ≤ Real.sqrt (C₂ * T ^ ε₀ * ((L + 2) * a)) * Real.sqrt (C₄ * T ^ ε₀ * ((L + 2) * b)) :=
          mul_le_mul (Real.sqrt_le_sqrt hsumA) (Real.sqrt_le_sqrt hsumB) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = Real.sqrt (C₂ * C₄) * (T ^ ε₀ * (L + 2)) * Real.sqrt (a * b) := by
          rw [← Real.sqrt_mul (by positivity)]
          rw [show C₂ * T ^ ε₀ * ((L + 2) * a) * (C₄ * T ^ ε₀ * ((L + 2) * b)) =
              (C₂ * C₄) * ((T ^ ε₀ * (L + 2)) ^ 2 * (a * b)) by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
            Real.sqrt_sq (by positivity)]
          ring
      _ ≤ Real.sqrt (C₂ * C₄) * (T ^ ε₀ * ((3 + 1 / ε₀) * T ^ ε₀)) * (6 * target) := by
          gcongr
      _ = K * T ^ ε * target := by rw [hK, hTε]; ring
  -- assemble
  have hsplit := sum_filter_add_sum_filter_not I (fun d => d ≤ N) G
  have hlarge' : (N : ℝ) * X ^ 3 ≤ T ^ ε * target := by
    have : (N : ℝ) * X ^ 3 ≤ target := by
      have : 0 ≤ N * T ^ (1 / 4 : ℝ) * X ^ (21 / 8 : ℝ) +
          Real.sqrt E * Real.sqrt X * (N : ℝ) ^ 2 := by positivity
      simp only [target]; linarith
    calc (N : ℝ) * X ^ 3 ≤ target := this
      _ ≤ T ^ ε * target := le_mul_of_one_le_left htarget0 (Real.one_le_rpow hT1 hε.le)
  calc ∑ p ∈ (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
          (fun p => (N : ℝ) ^ 2 / T ≤ ((Nat.gcd p.1 p.2 : ℕ) : ℝ)), ‖lagSum W ((p.1 : ℝ) / p.2)‖ ^ 3
      ≤ ∑ d ∈ I, G d := hreg
    _ = ∑ d ∈ Is, G d + ∑ d ∈ I.filter (fun d => ¬ d ≤ N), G d := hsplit.symm
    _ ≤ K * T ^ ε * target + T ^ ε * target := add_le_add hsmall (hlarge.trans hlarge')
    _ = (K + 1) * T ^ ε * target := by ring

end

end RHTower.GuthMaynard
