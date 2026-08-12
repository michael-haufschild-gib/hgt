import Mathlib

/-!
# Helson realization: the divisor-convolution response covector

The Helson matrix of a coefficient stream has entries `K_a(j,k) = a_{jk}`.  Its quadratic form at a
square-summable vector `u` is the divisor convolution `W_u(n) = ∑_{jk=n} conj(u_j) u_k`, which is
bounded by `‖u‖²` uniformly in `n` and is strictly positive at `m²` for the least index `m` with
`u_m ≠ 0`.  The divisor weight `d(n)` is the cardinality of the divisor antidiagonal, and the
weighted stream space `X_σ` is isometric to `ℓ¹_d` with a continuous total-mass functional whose
normalized differential is the centered exchange tangent.
-/

namespace HTGeometry.ConstraintMotiveRelativity

section Divisor

/-- **`(HFR.1)`.**  The divisor weight: the number of ordered factor pairs of `n`. -/
noncomputable def divisorWeight (n : ℕ) : ℕ := n.divisorsAntidiagonal.card

theorem divisorWeight_eq_card_divisors (n : ℕ) : divisorWeight n = n.divisors.card := by
  have h := Nat.sum_divisorsAntidiagonal (n := n) (fun _ _ => (1 : ℕ))
  simpa [divisorWeight] using h

/-- **`(HFR.1)`.**  The divisor-weighted coefficient space `ℓ¹_d`. -/
def HelsonSummable (a : ℕ → ℂ) : Prop :=
  Summable fun n : ℕ => (divisorWeight n : ℝ) * ‖a n‖

/-- **`(HFR.2)`.**  The Helson matrix entry. -/
noncomputable def helsonEntry (a : ℕ → ℂ) (j k : ℕ) : ℂ := a (j * k)

/-- **`(HFR.4)`.**  The realization is coefficient faithful: the first row recovers the stream. -/
@[simp] theorem helsonEntry_one_left (a : ℕ → ℂ) (n : ℕ) : helsonEntry a 1 n = a n := by
  rw [helsonEntry, one_mul]

/-- **Theorem 2.1 (3).**  A real stream gives a symmetric Helson matrix. -/
theorem helsonEntry_conj_symm {a : ℕ → ℂ} (ha : ∀ n, (starRingEnd ℂ) (a n) = a n) (j k : ℕ) :
    (starRingEnd ℂ) (helsonEntry a j k) = helsonEntry a k j := by
  rw [helsonEntry, helsonEntry, ha, mul_comm]

/-- **`(HFR.5)`.**  The absolute entry sum of the Helson matrix over one divisor fibre is the
divisor-weighted coefficient mass. -/
theorem sum_norm_helsonEntry_fibre (a : ℕ → ℂ) (n : ℕ) :
    ∑ p ∈ n.divisorsAntidiagonal, ‖helsonEntry a p.1 p.2‖ = (divisorWeight n : ℝ) * ‖a n‖ := by
  rw [divisorWeight]
  rw [Finset.sum_congr rfl fun p hp => ?_, Finset.sum_const, nsmul_eq_mul]
  rw [helsonEntry, (Nat.mem_divisorsAntidiagonal.mp hp).1]

end Divisor

section Response

/-- **`(HFR.6)`.**  The divisor-convolution response covector of a square-summable vector. -/
noncomputable def divisorConv (u : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ n.divisorsAntidiagonal, (starRingEnd ℂ) (u p.1) * u p.2

theorem tsum_normSq_lpTwo (u : lp (fun _ : ℕ => ℂ) 2) :
    ∑' n : ℕ, ‖(u : ℕ → ℂ) n‖ ^ 2 = ‖u‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) u
  simp only [ENNReal.toReal_ofNat] at h
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num] at h
  simp only [Real.rpow_natCast] at h
  rw [h]

theorem summable_normSq_lpTwo (u : lp (fun _ : ℕ => ℂ) 2) :
    Summable fun n : ℕ => ‖(u : ℕ → ℂ) n‖ ^ 2 := by
  have h := lp.memℓp u
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)] at h
  refine h.congr fun n => ?_
  rw [ENNReal.toReal_ofNat, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem sum_divisors_normSq_le (u : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    ∑ j ∈ n.divisors, ‖(u : ℕ → ℂ) j‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [← tsum_normSq_lpTwo u]
  exact (summable_normSq_lpTwo u).sum_le_tsum _ (fun i _ => sq_nonneg _)

/-- **Lemma 3.1.**  The divisor-convolution response is bounded by the squared norm, uniformly in
the atom. -/
theorem norm_divisorConv_le (u : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    ‖divisorConv (u : ℕ → ℂ) n‖ ≤ ‖u‖ ^ 2 := by
  classical
  have h1 : ‖divisorConv (u : ℕ → ℂ) n‖
      ≤ ∑ p ∈ n.divisorsAntidiagonal, ‖(u : ℕ → ℂ) p.1‖ * ‖(u : ℕ → ℂ) p.2‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
    rw [norm_mul, RCLike.norm_conj]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq n.divisorsAntidiagonal
    (fun p => ‖(u : ℕ → ℂ) p.1‖) (fun p => ‖(u : ℕ → ℂ) p.2‖)
  have hA : ∑ p ∈ n.divisorsAntidiagonal, ‖(u : ℕ → ℂ) p.1‖ ^ 2
      = ∑ j ∈ n.divisors, ‖(u : ℕ → ℂ) j‖ ^ 2 :=
    Nat.sum_divisorsAntidiagonal (fun j _ => ‖(u : ℕ → ℂ) j‖ ^ 2)
  have hB : ∑ p ∈ n.divisorsAntidiagonal, ‖(u : ℕ → ℂ) p.2‖ ^ 2
      = ∑ j ∈ n.divisors, ‖(u : ℕ → ℂ) j‖ ^ 2 := by
    rw [Nat.sum_divisorsAntidiagonal (fun _ k => ‖(u : ℕ → ℂ) k‖ ^ 2)]
    exact Nat.sum_div_divisors n fun j => ‖(u : ℕ → ℂ) j‖ ^ 2
  rw [hA, hB] at hcs
  have hle := sum_divisors_normSq_le u n
  have hsum0 : (0 : ℝ) ≤ ∑ p ∈ n.divisorsAntidiagonal,
      ‖(u : ℕ → ℂ) p.1‖ * ‖(u : ℕ → ℂ) p.2‖ :=
    Finset.sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [h1, hcs, hle, Finset.sum_nonneg (fun j (_ : j ∈ n.divisors) =>
    sq_nonneg ‖(u : ℕ → ℂ) j‖)]

/-- **Theorem 4.1 (4).**  The response covector is nonzero: at the square of the least active index
it equals the squared modulus of that coordinate. -/
theorem divisorConv_least_sq {u : ℕ → ℂ} {m : ℕ} (hm : 0 < m) (hum : u m ≠ 0)
    (hlt : ∀ j, 0 < j → j < m → u j = 0) :
    divisorConv u (m * m) = ((starRingEnd ℂ) (u m)) * u m := by
  classical
  rw [divisorConv]
  refine Finset.sum_eq_single (m, m) (fun p hp hne => ?_) (fun h => ?_)
  · obtain ⟨hmul, hnz⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hp1 : 0 < p.1 := Nat.pos_of_ne_zero fun h => by simp [h] at hmul; omega
    have hp2 : 0 < p.2 := Nat.pos_of_ne_zero fun h => by simp [h] at hmul; omega
    rcases lt_trichotomy p.1 m with h1 | h1 | h1
    · rw [hlt p.1 hp1 h1, map_zero, zero_mul]
    · exfalso
      apply hne
      have : p.2 = m := by
        have hm0 : m ≠ 0 := hm.ne'
        subst h1
        exact Nat.eq_of_mul_eq_mul_left hp1 hmul
      exact Prod.ext h1 this
    · have h2 : p.2 < m := by
        by_contra hcon
        push Not at hcon
        have hmm : m * m < p.1 * p.2 :=
          calc m * m ≤ m * p.2 := Nat.mul_le_mul_left m hcon
            _ < p.1 * p.2 := (Nat.mul_lt_mul_right hp2).mpr h1
        omega
      rw [hlt p.2 hp2 h2, mul_zero]
  · exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, by positivity⟩) h

end Response

section Normalized

variable {σ : ℝ}

/-- **`(HFR.10a)`.**  The Mellin-weighted stream norm. -/
noncomputable def mellinWeightedNorm (σ : ℝ) (x : ℕ → ℂ) : ℝ :=
  ∑' n : ℕ, (divisorWeight n : ℝ) * ‖x n‖ * ((n : ℝ) ^ σ)⁻¹

/-- **`(HFR.10a)`.**  The total mass functional. -/
noncomputable def mellinMass (σ : ℝ) (x : ℕ → ℂ) : ℂ := ∑' n : ℕ, x n * (((n : ℝ) ^ σ)⁻¹ : ℝ)

/-- **`(HFR.10a)`.**  The Mellin isometry `X_σ ≅ ℓ¹_d`. -/
theorem mellinWeightedNorm_eq (σ : ℝ) (x : ℕ → ℂ) :
    mellinWeightedNorm σ x
      = ∑' n : ℕ, (divisorWeight n : ℝ) * ‖x n * (((n : ℝ) ^ σ)⁻¹ : ℝ)‖ := by
  refine tsum_congr fun n => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((n : ℝ)) ^ σ)⁻¹)]
  ring

/-- **`(HFR.10a)`.**  The total mass is dominated by the weighted norm, since every divisor weight
of a nonzero index is at least one. -/
theorem norm_mellinMass_le (σ : ℝ) {x : ℕ → ℂ}
    (hx : Summable fun n : ℕ => ‖x n * (((n : ℝ) ^ σ)⁻¹ : ℝ)‖) (hx0 : x 0 = 0)
    (hw : Summable fun n : ℕ => (divisorWeight n : ℝ) * ‖x n * (((n : ℝ) ^ σ)⁻¹ : ℝ)‖) :
    ‖mellinMass σ x‖ ≤ mellinWeightedNorm σ x := by
  rw [mellinWeightedNorm_eq]
  refine (norm_tsum_le_tsum_norm hx).trans ?_
  refine hx.tsum_le_tsum (fun n => ?_) hw
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hx0]
  · have h1 : (1 : ℝ) ≤ (divisorWeight n : ℝ) := by
      have : 1 ≤ divisorWeight n := by
        rw [divisorWeight]
        refine Finset.card_pos.mpr ⟨(1, n), Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul n, hn.ne'⟩⟩
      exact_mod_cast this
    nlinarith [norm_nonneg (x n * (((n : ℝ) ^ σ)⁻¹ : ℝ))]

/-- **`(HFR.10)`.**  The normalized Mellin coefficient stream. -/
noncomputable def mellinNormalized (σ : ℝ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  (mellinMass σ c)⁻¹ * (c n * (((n : ℝ) ^ σ)⁻¹ : ℝ))

/-- **Corollary 5.1.**  The normalized stream is invariant under positive radial rescaling. -/
theorem mellinNormalized_smul {l : ℝ} (hl : l ≠ 0) (σ : ℝ) (c : ℕ → ℂ) (n : ℕ) :
    mellinNormalized σ (fun k => (l : ℂ) * c k) n = mellinNormalized σ c n := by
  have hlc : ((l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl
  have hmass : mellinMass σ (fun k => (l : ℂ) * c k) = (l : ℂ) * mellinMass σ c := by
    rw [mellinMass, mellinMass, ← tsum_mul_left]
    exact tsum_congr fun k => by ring
  rw [mellinNormalized, mellinNormalized, hmass, mul_inv]
  field_simp

/-- **`(HFR.11)`.**  The exchange tangent of the normalization at a stream with nonzero mass. -/
noncomputable def mellinExchangeSeed (σ : ℝ) (c h : ℕ → ℂ) (n : ℕ) : ℂ :=
  (((n : ℝ) ^ σ)⁻¹ : ℝ) * (mellinMass σ c)⁻¹
    * (h n - (mellinMass σ h) * (mellinMass σ c)⁻¹ * c n)

/-- **`(HFR.11)`.**  The exchange tangent is the coordinatewise derivative of the normalization
along an additive-mass direction. -/
theorem hasDerivAt_mellinNormalized {σ : ℝ} {c h : ℕ → ℂ} (hZ : mellinMass σ c ≠ 0)
    (hlin : ∀ e : ℂ, mellinMass σ (fun k => c k + e * h k) = mellinMass σ c + e * mellinMass σ h)
    (n : ℕ) :
    HasDerivAt (fun e : ℂ => mellinNormalized σ (fun k => c k + e * h k) n)
      (mellinExchangeSeed σ c h n) 0 := by
  have hfun : (fun e : ℂ => mellinNormalized σ (fun k => c k + e * h k) n)
      = fun e : ℂ => (mellinMass σ c + e * mellinMass σ h)⁻¹
        * ((c n + e * h n) * (((n : ℝ) ^ σ)⁻¹ : ℝ)) := by
    funext e
    rw [mellinNormalized, hlin e]
  rw [hfun]
  have hden : HasDerivAt (fun e : ℂ => mellinMass σ c + e * mellinMass σ h) (mellinMass σ h) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (mellinMass σ h)).const_add (mellinMass σ c)
  have hden0 : (mellinMass σ c + (0 : ℂ) * mellinMass σ h) ≠ 0 := by simpa using hZ
  have hnum : HasDerivAt (fun e : ℂ => (c n + e * h n) * (((n : ℝ) ^ σ)⁻¹ : ℝ))
      (h n * (((n : ℝ) ^ σ)⁻¹ : ℝ)) 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).mul_const (h n)).const_add (c n)).mul_const
      ((((n : ℝ) ^ σ)⁻¹ : ℝ) : ℂ)
  have hmul := (hden.inv hden0).mul hnum
  refine HasDerivAt.congr_deriv hmul ?_
  simp only [mellinExchangeSeed, zero_mul, add_zero, Pi.inv_apply]
  field_simp
  ring

end Normalized

section Countermodel

/-- **§6, countermodel 1.**  Coefficient positivity does not imply operator positivity: the
Helson block of the stream supported at `2` is the reflection `[[0,1],[1,0]]`, whose eigenvalues
are `1` and `-1`. -/
theorem helson_block_not_posSemidef :
    ∃ a : ℕ → ℂ, (∀ n, 0 ≤ (a n).re ∧ (a n).im = 0) ∧
      ¬ (0 ≤ (helsonEntry a 1 1 * ((-1 : ℂ)) * ((-1 : ℂ))
        + helsonEntry a 1 2 * ((-1 : ℂ)) * 1
        + helsonEntry a 2 1 * 1 * ((-1 : ℂ))
        + helsonEntry a 2 2 * 1 * 1).re) := by
  classical
  refine ⟨fun n => if n = 2 then 1 else 0, fun n => ?_, ?_⟩
  · by_cases h : n = 2 <;> simp [h]
  · simp only [helsonEntry]
    norm_num

end Countermodel

end HTGeometry.ConstraintMotiveRelativity
