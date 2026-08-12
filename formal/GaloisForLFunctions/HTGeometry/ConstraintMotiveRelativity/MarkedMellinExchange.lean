import Mathlib
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator

/-!
# Marked Mellin normalization exchange and phase response

A nonnegative coefficient stream `c` with all logarithmic moments finite carries three reporters:
the Mellin series `S_c`, the marked positive pair `(Z_c, P_c)`, and the phase correlation `C_c`.
The marked pair is coefficient faithful, while the unmarked probability is invariant under positive
radial rescaling.

Normalization exchanges source scale for centered mass: its directional derivative is
`Z_c^{-1}(μ_h − H₀(h) P_c)`, which has total mass zero and vanishes exactly on the radial line.
The induced phase response is the centered character response, predicted by the marked reporter and
the current correlation rather than fitted, and the normalized state alone cannot predict the
absolute response.
-/

namespace HTGeometry.ConstraintMotiveRelativity

open Filter Topology

section MarkedMellin

variable {σ : ℝ}

/-- The atomic Mellin weight of a coefficient at abscissa `σ`. -/
noncomputable def mellinWeight (σ : ℝ) (h : ℕ → ℝ) (n : ℕ) : ℝ := h n * (n : ℝ) ^ (-σ)

/-- **`(MER.5)`, `(MER.9)`.**  The total mass of the atomic measure. -/
noncomputable def totalMass (σ : ℝ) (h : ℕ → ℝ) : ℝ := ∑' n, mellinWeight σ h n

/-- **`(MER.6)`.**  The normalized atomic weight. -/
noncomputable def normWeight (σ : ℝ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  mellinWeight σ c n / totalMass σ c

/-- **`(MER.7)`.**  The marked pair is coefficient faithful. -/
theorem coeff_of_normWeight {c : ℕ → ℝ} {n : ℕ} (hn : 0 < n) (hZ : totalMass σ c ≠ 0) :
    c n = totalMass σ c * (n : ℝ) ^ σ * normWeight σ c n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [normWeight, mellinWeight, div_eq_mul_inv]
  field_simp
  rw [Real.rpow_neg hn0.le]
  field_simp

/-- Total mass is positively homogeneous. -/
theorem totalMass_smul (l : ℝ) (c : ℕ → ℝ) :
    totalMass σ (fun n => l * c n) = l * totalMass σ c := by
  rw [totalMass, totalMass, ← tsum_mul_left]
  exact tsum_congr fun n => by rw [mellinWeight, mellinWeight]; ring

/-- **The unmarked probability is invariant under positive radial rescaling.** -/
theorem normWeight_smul {l : ℝ} (hl : l ≠ 0) (c : ℕ → ℝ) (n : ℕ) :
    normWeight σ (fun n => l * c n) n = normWeight σ c n := by
  rw [normWeight, normWeight, totalMass_smul, mellinWeight, mellinWeight]
  rw [show l * c n * (n : ℝ) ^ (-σ) = l * (c n * (n : ℝ) ^ (-σ)) by ring]
  rw [mul_div_mul_left _ _ hl]

/-- **`(MER.10)`.**  The exchange seed: the derivative of the normalized weight. -/
noncomputable def exchangeSeed (σ : ℝ) (c h : ℕ → ℝ) (n : ℕ) : ℝ :=
  (mellinWeight σ h n - totalMass σ h * normWeight σ c n) / totalMass σ c

/-- **Theorem 3.1, `(MER.10)`.**  The exchange seed is the coordinatewise derivative of the
normalization along the affine path `c + ε h`. -/
theorem hasDerivAt_normWeight {c h : ℕ → ℝ} (hZ : totalMass σ c ≠ 0)
    (hlin : ∀ e : ℝ, totalMass σ (fun n => c n + e * h n) = totalMass σ c + e * totalMass σ h)
    (n : ℕ) :
    HasDerivAt (fun e : ℝ => normWeight σ (fun n => c n + e * h n) n) (exchangeSeed σ c h n) 0 := by
  have hnum : HasDerivAt (fun e : ℝ => mellinWeight σ (fun n => c n + e * h n) n)
      (mellinWeight σ h n) 0 := by
    have hb : HasDerivAt (fun e : ℝ => c n + e * h n) (h n) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (h n)).const_add (c n)
    have := hb.mul_const ((n : ℝ) ^ (-σ))
    simpa [mellinWeight] using this
  have hden : HasDerivAt (fun e : ℝ => totalMass σ (fun n => c n + e * h n))
      (totalMass σ h) 0 := by
    have hb : HasDerivAt (fun e : ℝ => totalMass σ c + e * totalMass σ h) (totalMass σ h) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (totalMass σ h)).const_add (totalMass σ c)
    exact hb.congr_of_eventuallyEq (Filter.Eventually.of_forall fun e => hlin e)
  have hden0 : (fun e : ℝ => totalMass σ (fun n => c n + e * h n)) 0 ≠ 0 := by
    simpa using hZ
  have hdiv := hnum.div hden hden0
  have hval : exchangeSeed σ c h n
      = (mellinWeight σ h n * totalMass σ c - mellinWeight σ c n * totalMass σ h)
        / totalMass σ c ^ 2 := by
    simp only [exchangeSeed, normWeight, mellinWeight]
    field_simp
  rw [hval]
  have hsimp : ∀ n : ℕ, c n + (0 : ℝ) * h n = c n := fun n => by ring
  simp only [hsimp] at hdiv
  exact hdiv

/-- The normalized weights have total mass one. -/
theorem tsum_normWeight {c : ℕ → ℝ} (hZ : totalMass σ c ≠ 0) :
    ∑' n, normWeight σ c n = 1 := by
  have h : ∑' n, normWeight σ c n = (∑' n, mellinWeight σ c n) * (totalMass σ c)⁻¹ := by
    simp only [normWeight, div_eq_mul_inv]
    exact tsum_mul_right
  rw [h, ← totalMass, mul_inv_cancel₀ hZ]

/-- **Theorem 3.1, mass zero.**  The exchange seed has total mass zero: normalization exchanges
source scale for centered mass. -/
theorem tsum_exchangeSeed {c h : ℕ → ℝ} (hZ : totalMass σ c ≠ 0)
    (hs : Summable fun n => mellinWeight σ h n)
    (hc : Summable fun n => mellinWeight σ c n) :
    ∑' n, exchangeSeed σ c h n = 0 := by
  classical
  have hnw : Summable fun n => totalMass σ h * normWeight σ c n := by
    refine (hc.mul_left (totalMass σ h * (totalMass σ c)⁻¹)).congr fun n => ?_
    simp only [normWeight, div_eq_mul_inv]
    ring
  have hsplit : ∑' n, exchangeSeed σ c h n
      = (∑' n, (mellinWeight σ h n - totalMass σ h * normWeight σ c n)) * (totalMass σ c)⁻¹ := by
    simp only [exchangeSeed, div_eq_mul_inv]
    exact tsum_mul_right
  rw [hsplit, hs.tsum_sub hnw, tsum_mul_left, tsum_normWeight hZ, mul_one, ← totalMass,
    sub_self, zero_mul]

/-- **Theorem 3.1, `(MER.11)`.**  The exchange seed vanishes exactly on the radial line. -/
theorem exchangeSeed_eq_zero_iff {c h : ℕ → ℝ} (hZ : totalMass σ c ≠ 0) :
    (∀ n, 0 < n → exchangeSeed σ c h n = 0) ↔ ∀ n, 0 < n → h n = totalMass σ h / totalMass σ c * c n := by
  constructor
  · intro hzero n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hpow : ((n : ℝ) ^ (-σ)) ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
    have h0 := hzero n hn
    simp only [exchangeSeed, normWeight, mellinWeight, div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · have h1 : h n * (n : ℝ) ^ (-σ)
          = totalMass σ h * (c n * (n : ℝ) ^ (-σ) / totalMass σ c) := by linarith
      field_simp at h1 ⊢
      linarith [h1]
    · exact absurd h0 hZ
  · intro hrad n hn
    have h0 := hrad n hn
    simp only [exchangeSeed, normWeight, mellinWeight, h0]
    field_simp
    ring

/-! ### The phase reporter and its response -/

/-- The prime-log atom of a coordinate. -/
noncomputable def logAtom (n : ℕ) : ℝ := Real.log n

/-- The character evaluated at an atom. -/
noncomputable def atomChar (t : ℝ) (n : ℕ) : ℂ := Complex.exp (-(Complex.I * ((t * logAtom n : ℝ) : ℂ)))

/-- **`(MER.6)`.**  The phase correlation of a marked source. -/
noncomputable def phaseCorr (σ : ℝ) (c : ℕ → ℝ) (t : ℝ) : ℂ :=
  (∑' n, (mellinWeight σ c n : ℂ) * atomChar t n) / (totalMass σ c : ℂ)

/-- **`(MER.13)`.**  The centered phase response to an intervention. -/
noncomputable def phaseResponse (σ : ℝ) (c h : ℕ → ℝ) (t : ℝ) : ℂ :=
  (∑' n, (mellinWeight σ h n : ℂ) * (atomChar t n - phaseCorr σ c t)) / (totalMass σ c : ℂ)

/-- **`(MER.19)`.**  The phase reporter is radial-scale invariant. -/
theorem phaseCorr_smul {l : ℝ} (hl : l ≠ 0) (c : ℕ → ℝ) (t : ℝ) :
    phaseCorr σ (fun n => l * c n) t = phaseCorr σ c t := by
  have hnum : ∑' n, (mellinWeight σ (fun n => l * c n) n : ℂ) * atomChar t n
      = (l : ℂ) * ∑' n, (mellinWeight σ c n : ℂ) * atomChar t n := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [mellinWeight]
    push_cast
    ring
  have hlc : ((l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl
  rw [phaseCorr, phaseCorr, hnum, totalMass_smul]
  push_cast
  rw [mul_div_mul_left _ _ hlc]

/-- **`(MER.20)`.**  The same absolute intervention has response scaled by `λ⁻¹`: the unmarked
reporters cannot predict the absolute response. -/
theorem phaseResponse_smul {l : ℝ} (hl : l ≠ 0) (c h : ℕ → ℝ) (t : ℝ) :
    phaseResponse σ (fun n => l * c n) h t = (l : ℂ)⁻¹ * phaseResponse σ c h t := by
  have hlc : ((l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl
  rw [phaseResponse, phaseResponse, phaseCorr_smul hl, totalMass_smul]
  push_cast
  rw [mul_comm ((l : ℂ)) ((totalMass σ c : ℂ)), div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-- **`(MER.15)`.**  The response to a multiplicative atom intervention is the marked weight times
the centered character. -/
theorem phaseResponse_atom {c : ℕ → ℝ} (hZ : totalMass σ c ≠ 0) (N : ℕ) (t : ℝ) :
    phaseResponse σ c (fun m => if m = N then c N else 0) t
      = (normWeight σ c N : ℂ) * (atomChar t N - phaseCorr σ c t) := by
  classical
  have hz : ∀ m, m ≠ N →
      (mellinWeight σ (fun m => if m = N then c N else 0) m : ℂ)
        * (atomChar t m - phaseCorr σ c t) = 0 := by
    intro m hm
    simp [mellinWeight, hm]
  have hZc : ((totalMass σ c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hZ
  rw [phaseResponse, tsum_eq_single N hz]
  have hval : (mellinWeight σ (fun m => if m = N then c N else 0) N : ℂ)
      = (mellinWeight σ c N : ℂ) := by
    simp [mellinWeight]
  rw [hval, normWeight, div_eq_mul_inv]
  push_cast
  field_simp

/-! ### Atomic source density -/

/-- **Theorem 1.1.**  A morphism of atomic probe nerves exists exactly when the source dominates
coordinatewise; hom-sets in the source poset are empty or singletons, so the morphism is unique. -/
theorem atomic_density {c d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n) :
    (∀ (n : ℕ) (q : ℚ), 0 < q → (q : ℝ) ≤ c n → (q : ℝ) ≤ d n) ↔ ∀ n, c n ≤ d n := by
  constructor
  · intro hdom n
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hqpos : (0 : ℚ) < q := by
      have : (0 : ℝ) < (q : ℝ) := lt_of_le_of_lt (hd n) hq1
      exact_mod_cast this
    exact absurd (hdom n q hqpos hq2.le) (not_le.2 hq1)
  · intro hle n q _ hqc
    exact le_trans hqc (hle n)

/-- The coordinate is the supremum of the rational probes below it. -/
theorem coeff_eq_sSup {c : ℕ → ℝ} {n : ℕ} (hc : 0 ≤ c n) :
    IsLUB ({0} ∪ {x : ℝ | ∃ q : ℚ, 0 < q ∧ (x : ℝ) = q ∧ (q : ℝ) ≤ c n}) (c n) := by
  constructor
  · rintro x (hx | ⟨q, hq, rfl, hqc⟩)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact hc
    · exact hqc
  · intro y hy
    have h0 : (0 : ℝ) ≤ y := hy (Or.inl rfl)
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    have hqpos : (0 : ℚ) < q := by exact_mod_cast lt_of_le_of_lt h0 hq1
    exact absurd (hy (Or.inr ⟨q, hqpos, rfl, hq2.le⟩)) (by push Not; exact hq1)

/-! ### Expectation, covariance and the Fisher bound -/

/-- Expectation against the normalized weights. -/
noncomputable def expect (σ : ℝ) (c : ℕ → ℝ) (f : ℕ → ℂ) : ℂ :=
  ∑' n, (normWeight σ c n : ℂ) * f n

theorem expect_const (σ : ℝ) (c : ℕ → ℝ) (a : ℂ) :
    expect σ c (fun _ => a) = (∑' n, (normWeight σ c n : ℂ)) * a := by
  rw [expect, ← tsum_mul_right]

/-- **`(MER.6)`.**  The phase correlation is the expectation of the character. -/
theorem phaseCorr_eq_expect {c : ℕ → ℝ} (hZ : totalMass σ c ≠ 0) (t : ℝ) :
    phaseCorr σ c t = expect σ c (atomChar t) := by
  have hZc : ((totalMass σ c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hZ
  rw [phaseCorr, expect, div_eq_mul_inv, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [normWeight, div_eq_mul_inv]
  push_cast
  ring

/-- **`(MER.14)`.**  For a multiplicative score the response is the bilinear covariance of the
score against the phase character. -/
theorem phaseResponse_covariance {c r : ℕ → ℝ} (hZ : totalMass σ c ≠ 0) (t : ℝ)
    (hs1 : Summable fun n => (normWeight σ c n : ℂ) * ((r n : ℂ) * atomChar t n))
    (hs2 : Summable fun n => (normWeight σ c n : ℂ) * (r n : ℂ)) :
    phaseResponse σ c (fun n => c n * r n) t
      = expect σ c (fun n => (r n : ℂ) * atomChar t n)
        - expect σ c (fun n => (r n : ℂ)) * phaseCorr σ c t := by
  have hZc : ((totalMass σ c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hZ
  have hterm : ∀ n : ℕ,
      (mellinWeight σ (fun n => c n * r n) n : ℂ) * (atomChar t n - phaseCorr σ c t)
        * ((totalMass σ c : ℝ) : ℂ)⁻¹
        = (normWeight σ c n : ℂ) * ((r n : ℂ) * atomChar t n)
          - (normWeight σ c n : ℂ) * (r n : ℂ) * phaseCorr σ c t := by
    intro n
    simp only [mellinWeight, normWeight]
    push_cast
    field_simp
  rw [phaseResponse, div_eq_mul_inv, ← tsum_mul_right, tsum_congr hterm,
    hs1.tsum_sub (hs2.mul_right (phaseCorr σ c t)), tsum_mul_right]
  rfl

/-- The `P_c`-variance of a real score. -/
noncomputable def variance (σ : ℝ) (c : ℕ → ℝ) (r : ℕ → ℝ) : ℂ :=
  expect σ c (fun n => ((r n : ℂ)) ^ 2) - (expect σ c (fun n => (r n : ℂ))) ^ 2

/-- The Hermitian variance of the phase character. -/
noncomputable def hermVarianceChar (σ : ℝ) (c : ℕ → ℝ) (t : ℝ) : ℂ :=
  expect σ c (fun n => atomChar t n * (starRingEnd ℂ) (atomChar t n))
    - phaseCorr σ c t * (starRingEnd ℂ) (phaseCorr σ c t)

@[simp] theorem atomChar_mul_conj (t : ℝ) (n : ℕ) :
    atomChar t n * (starRingEnd ℂ) (atomChar t n) = 1 := by
  have h : ‖atomChar t n‖ = 1 := by
    rw [atomChar, Complex.norm_exp]
    simp
  have := Complex.mul_conj (atomChar t n)
  rw [this, Complex.normSq_eq_norm_sq, h]
  norm_num

/-- **`(MER.17)`, the variance identity.**  The Hermitian variance of the character is
`1 - |C_c(t)|²`. -/
theorem hermVarianceChar_eq {c : ℕ → ℝ} (t : ℝ)
    (hone : ∑' n, (normWeight σ c n : ℂ) = 1) :
    hermVarianceChar σ c t = 1 - (‖phaseCorr σ c t‖ ^ 2 : ℝ) := by
  have h1 : expect σ c (fun n => atomChar t n * (starRingEnd ℂ) (atomChar t n)) = 1 := by
    rw [expect]
    simp only [atomChar_mul_conj, mul_one]
    exact hone
  rw [hermVarianceChar, h1, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-! ### The marked probability state -/

/-- The standing marked hypotheses: the normalized atomic weights form a probability vector. -/
structure IsMarkedState (σ : ℝ) (c : ℕ → ℝ) : Prop where
  /-- The normalized weights are nonnegative. -/
  nonneg : ∀ n, 0 ≤ normWeight σ c n
  /-- The normalized weights are summable. -/
  summable : Summable (normWeight σ c)
  /-- The normalized weights carry total mass one. -/
  total : ∑' n, normWeight σ c n = 1

namespace IsMarkedState

variable {c : ℕ → ℝ}

/-- A marked state has nonzero total mass: a vanishing mass normalizes every weight to zero. -/
theorem totalMass_ne_zero (hc : IsMarkedState σ c) : totalMass σ c ≠ 0 := by
  intro h
  have hz : ∀ n, normWeight σ c n = 0 := fun n => by rw [normWeight, h, div_zero]
  have h1 := hc.total
  rw [tsum_congr hz, tsum_zero] at h1
  exact zero_ne_one h1

theorem summable_complex (hc : IsMarkedState σ c) :
    Summable fun n => ((normWeight σ c n : ℝ) : ℂ) :=
  Summable.of_norm_bounded hc.summable fun n => le_of_eq (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc.nonneg n)])

theorem total_complex (hc : IsMarkedState σ c) :
    ∑' n, ((normWeight σ c n : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_tsum, hc.total, Complex.ofReal_one]

/-- A uniformly bounded observable is `P_c`-summable. -/
theorem summable_mul_of_bounded (hc : IsMarkedState σ c) {f : ℕ → ℂ} {M : ℝ}
    (hf : ∀ n, ‖f n‖ ≤ M) : Summable fun n => ((normWeight σ c n : ℝ) : ℂ) * f n := by
  refine Summable.of_norm_bounded (hc.summable.mul_right M) fun n => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc.nonneg n)]
  exact mul_le_mul_of_nonneg_left (hf n) (hc.nonneg n)

end IsMarkedState

@[simp] theorem norm_atomChar (t : ℝ) (n : ℕ) : ‖atomChar t n‖ = 1 := by
  rw [atomChar, Complex.norm_exp]
  simp

theorem norm_atomChar_sub_le (σ : ℝ) (c : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    ‖atomChar t n - phaseCorr σ c t‖ ≤ 1 + ‖phaseCorr σ c t‖ := by
  simpa using norm_sub_le (atomChar t n) (phaseCorr σ c t)

namespace IsMarkedState

variable {c : ℕ → ℝ}

theorem summable_atomChar (hc : IsMarkedState σ c) (t : ℝ) :
    Summable fun n => ((normWeight σ c n : ℝ) : ℂ) * atomChar t n :=
  hc.summable_mul_of_bounded (M := 1) fun n => (norm_atomChar t n).le

theorem expect_atomChar (hc : IsMarkedState σ c) (t : ℝ) :
    expect σ c (atomChar t) = phaseCorr σ c t :=
  (phaseCorr_eq_expect hc.totalMass_ne_zero t).symm

theorem tsum_normWeight_mul_atomChar (hc : IsMarkedState σ c) (t : ℝ) :
    ∑' n, ((normWeight σ c n : ℝ) : ℂ) * atomChar t n = phaseCorr σ c t :=
  (phaseCorr_eq_expect hc.totalMass_ne_zero t).symm

theorem summable_centered_atomChar (hc : IsMarkedState σ c) (t : ℝ) :
    Summable fun n => ((normWeight σ c n : ℝ) : ℂ) * (atomChar t n - phaseCorr σ c t) :=
  hc.summable_mul_of_bounded (M := 1 + ‖phaseCorr σ c t‖) fun n => norm_atomChar_sub_le σ c t n

end IsMarkedState

/-- The centered phase character has zero `P_c`-mean. -/
theorem tsum_centered_atomChar {c : ℕ → ℝ} (hc : IsMarkedState σ c) (t : ℝ) :
    ∑' n, ((normWeight σ c n : ℝ) : ℂ) * (atomChar t n - phaseCorr σ c t) = 0 := by
  have hterm : ∀ n : ℕ, ((normWeight σ c n : ℝ) : ℂ) * (atomChar t n - phaseCorr σ c t)
      = ((normWeight σ c n : ℝ) : ℂ) * atomChar t n
        - ((normWeight σ c n : ℝ) : ℂ) * phaseCorr σ c t := fun n => by ring
  rw [tsum_congr hterm, (hc.summable_atomChar t).tsum_sub
      (hc.summable_complex.mul_right (phaseCorr σ c t)),
    hc.tsum_normWeight_mul_atomChar t, tsum_mul_right, hc.total_complex, one_mul, sub_self]

/-! ### The Fisher form -/

/-- The `P_c`-mean of a real score. -/
noncomputable def mean (σ : ℝ) (c r : ℕ → ℝ) : ℝ := ∑' n, normWeight σ c n * r n

/-- **`(MER.16)`.**  The quotient Fisher form of a real score: its `P_c`-variance. -/
noncomputable def fisherVar (σ : ℝ) (c r : ℕ → ℝ) : ℝ :=
  ∑' n, normWeight σ c n * (r n - mean σ c r) ^ 2

/-- The Hermitian `P_c`-variance of a complex observable. -/
noncomputable def hermVar (σ : ℝ) (c : ℕ → ℝ) (f : ℕ → ℂ) : ℝ :=
  ∑' n, normWeight σ c n * ‖f n - expect σ c f‖ ^ 2

theorem fisherVar_nonneg {c : ℕ → ℝ} (hc : IsMarkedState σ c) (r : ℕ → ℝ) :
    0 ≤ fisherVar σ c r :=
  tsum_nonneg fun n => mul_nonneg (hc.nonneg n) (sq_nonneg _)

theorem hermVar_nonneg {c : ℕ → ℝ} (hc : IsMarkedState σ c) (f : ℕ → ℂ) :
    0 ≤ hermVar σ c f :=
  tsum_nonneg fun n => mul_nonneg (hc.nonneg n) (sq_nonneg _)

/-- **`(MER.17)`, the character variance.**  `Var^H_{P_c}(e^{-itx}) = 1 - |C_c(t)|²`, because the
character has modulus one and its `P_c`-mean is the phase correlation. -/
theorem hermVar_atomChar {c : ℕ → ℝ} (hc : IsMarkedState σ c) (t : ℝ) :
    hermVar σ c (atomChar t) = 1 - ‖phaseCorr σ c t‖ ^ 2 := by
  have hE : expect σ c (atomChar t) = phaseCorr σ c t := hc.expect_atomChar t
  have hu : ∀ n : ℕ, normWeight σ c n * ‖atomChar t n - phaseCorr σ c t‖ ^ 2
      = normWeight σ c n * (1 + ‖phaseCorr σ c t‖ ^ 2)
        - 2 * (normWeight σ c n
            * (atomChar t n * (starRingEnd ℂ) (phaseCorr σ c t)).re) := by
    intro n
    have h := Complex.normSq_sub (atomChar t n) (phaseCorr σ c t)
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      norm_atomChar] at h
    rw [h]
    ring
  have hbound : ∀ n : ℕ,
      |(atomChar t n * (starRingEnd ℂ) (phaseCorr σ c t)).re| ≤ ‖phaseCorr σ c t‖ := by
    intro n
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_atomChar, one_mul, Complex.norm_conj]
  have hsum1 : Summable fun n => normWeight σ c n * (1 + ‖phaseCorr σ c t‖ ^ 2) :=
    hc.summable.mul_right _
  have hsum2 : Summable fun n => 2 * (normWeight σ c n
      * (atomChar t n * (starRingEnd ℂ) (phaseCorr σ c t)).re) := by
    refine Summable.of_norm_bounded (hc.summable.mul_right (2 * ‖phaseCorr σ c t‖)) fun n => ?_
    have h1 : |2 * (normWeight σ c n
        * (atomChar t n * (starRingEnd ℂ) (phaseCorr σ c t)).re)|
        = 2 * (normWeight σ c n
            * |(atomChar t n * (starRingEnd ℂ) (phaseCorr σ c t)).re|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hc.nonneg n)]
      norm_num
    rw [Real.norm_eq_abs, h1]
    nlinarith [hbound n, hc.nonneg n, norm_nonneg (phaseCorr σ c t)]
  have hval : ∑' n, normWeight σ c n
      * (atomChar t n * (starRingEnd ℂ) (phaseCorr σ c t)).re = ‖phaseCorr σ c t‖ ^ 2 := by
    have hterm : ∀ n : ℕ, normWeight σ c n
        * (atomChar t n * (starRingEnd ℂ) (phaseCorr σ c t)).re
        = (((normWeight σ c n : ℝ) : ℂ) * atomChar t n
            * (starRingEnd ℂ) (phaseCorr σ c t)).re := by
      intro n
      rw [mul_assoc, Complex.re_ofReal_mul]
    have hsc : Summable fun n => ((normWeight σ c n : ℝ) : ℂ) * atomChar t n
        * (starRingEnd ℂ) (phaseCorr σ c t) :=
      (hc.summable_atomChar t).mul_right _
    rw [tsum_congr hterm, ← Complex.re_tsum hsc, tsum_mul_right,
      hc.tsum_normWeight_mul_atomChar t, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  rw [hermVar, hE, tsum_congr hu, hsum1.tsum_sub hsum2, tsum_mul_right, hc.total, one_mul,
    tsum_mul_left, hval]
  ring

/-! ### The centered response and the Fisher bound -/

/-- The multiplicative response is the `P_c`-covariance of the centered score against the centered
character, for every centering constant. -/
theorem phaseResponse_centered {c r : ℕ → ℝ} (hc : IsMarkedState σ c)
    (hr : Summable fun n => normWeight σ c n * |r n|) (m : ℝ) (t : ℝ) :
    phaseResponse σ c (fun n => c n * r n) t
      = ∑' n, ((normWeight σ c n : ℝ) : ℂ) * ((r n - m : ℝ) : ℂ)
          * (atomChar t n - phaseCorr σ c t) := by
  have hZ := hc.totalMass_ne_zero
  have hZc : ((totalMass σ c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hZ
  have hsm : Summable fun n => normWeight σ c n * |r n - m| := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hc.nonneg n) (abs_nonneg _)) ?_
      (hr.add (hc.summable.mul_right |m|))
    intro n
    have h1 : |r n - m| ≤ |r n| + |m| := by
      simpa [sub_eq_add_neg] using abs_add_le (r n) (-m)
    nlinarith [hc.nonneg n, abs_nonneg (r n), abs_nonneg m]
  have hS0 : Summable fun n => ((normWeight σ c n : ℝ) : ℂ) * ((r n : ℝ) : ℂ)
      * (atomChar t n - phaseCorr σ c t) := by
    refine Summable.of_norm_bounded (hr.mul_right (1 + ‖phaseCorr σ c t‖)) fun n => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (hc.nonneg n)]
    nlinarith [norm_atomChar_sub_le σ c t n,
      mul_nonneg (hc.nonneg n) (abs_nonneg (r n))]
  have hS2 := hc.summable_centered_atomChar t
  have hsplit : ∀ n : ℕ, ((normWeight σ c n : ℝ) : ℂ) * ((r n - m : ℝ) : ℂ)
      * (atomChar t n - phaseCorr σ c t)
      = ((normWeight σ c n : ℝ) : ℂ) * ((r n : ℝ) : ℂ) * (atomChar t n - phaseCorr σ c t)
        - (m : ℂ) * (((normWeight σ c n : ℝ) : ℂ) * (atomChar t n - phaseCorr σ c t)) := by
    intro n
    push_cast
    ring
  have hterm : ∀ n : ℕ,
      ((mellinWeight σ (fun n => c n * r n) n : ℝ) : ℂ) * (atomChar t n - phaseCorr σ c t)
          * ((totalMass σ c : ℝ) : ℂ)⁻¹
        = ((normWeight σ c n : ℝ) : ℂ) * ((r n : ℝ) : ℂ)
            * (atomChar t n - phaseCorr σ c t) := by
    intro n
    simp only [mellinWeight, normWeight]
    push_cast
    field_simp
  rw [phaseResponse, div_eq_mul_inv, ← tsum_mul_right, tsum_congr hterm, tsum_congr hsplit,
    hS0.tsum_sub (hS2.mul_left (m : ℂ)), tsum_mul_left, tsum_centered_atomChar hc t,
    mul_zero, sub_zero]

/-- **`(MER.17)`.**  Weighted Cauchy–Schwarz: the quotient Fisher seminorm dominates every phase
character response, with the sharp character factor `1 - |C_c(t)|²`. -/
theorem phaseResponse_normSq_le {c r : ℕ → ℝ} (hc : IsMarkedState σ c)
    (hr : Summable fun n => normWeight σ c n * |r n|)
    (hr2 : Summable fun n => normWeight σ c n * r n ^ 2) (t : ℝ) :
    ‖phaseResponse σ c (fun n => c n * r n) t‖ ^ 2
      ≤ fisherVar σ c r * (1 - ‖phaseCorr σ c t‖ ^ 2) := by
  have hwr : Summable fun n => normWeight σ c n * r n := by
    refine Summable.of_norm_bounded hr fun n => le_of_eq ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc.nonneg n)]
  have hsm : Summable fun n => normWeight σ c n * |r n - mean σ c r| := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hc.nonneg n) (abs_nonneg _)) ?_
      (hr.add (hc.summable.mul_right |mean σ c r|))
    intro n
    have h1 : |r n - mean σ c r| ≤ |r n| + |mean σ c r| := by
      simpa [sub_eq_add_neg] using abs_add_le (r n) (-(mean σ c r))
    nlinarith [hc.nonneg n, abs_nonneg (r n), abs_nonneg (mean σ c r)]
  have hFV : Summable fun n => normWeight σ c n * (r n - mean σ c r) ^ 2 := by
    have hs := (hr2.sub (hwr.mul_left (2 * mean σ c r))).add
      (hc.summable.mul_left (mean σ c r ^ 2))
    refine hs.congr fun n => ?_
    ring
  have hHV : Summable fun n => normWeight σ c n * ‖atomChar t n - phaseCorr σ c t‖ ^ 2 := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hc.nonneg n) (sq_nonneg _)) ?_
      (hc.summable.mul_right ((1 + ‖phaseCorr σ c t‖) ^ 2))
    intro n
    have h3 : ‖atomChar t n - phaseCorr σ c t‖ ^ 2 ≤ (1 + ‖phaseCorr σ c t‖) ^ 2 := by
      nlinarith [norm_atomChar_sub_le σ c t n, norm_nonneg (atomChar t n - phaseCorr σ c t)]
    exact mul_le_mul_of_nonneg_left h3 (hc.nonneg n)
  have hA : Summable fun n => (Real.sqrt (normWeight σ c n) * |r n - mean σ c r|) ^ 2 :=
    hFV.congr fun n => by rw [mul_pow, Real.sq_sqrt (hc.nonneg n), sq_abs]
  have hB : Summable fun n =>
      (Real.sqrt (normWeight σ c n) * ‖atomChar t n - phaseCorr σ c t‖) ^ 2 :=
    hHV.congr fun n => by rw [mul_pow, Real.sq_sqrt (hc.nonneg n)]
  have hA' : ∑' n, (Real.sqrt (normWeight σ c n) * |r n - mean σ c r|) ^ 2
      = fisherVar σ c r := by
    rw [fisherVar]
    exact tsum_congr fun n => by rw [mul_pow, Real.sq_sqrt (hc.nonneg n), sq_abs]
  have hB' : ∑' n, (Real.sqrt (normWeight σ c n) * ‖atomChar t n - phaseCorr σ c t‖) ^ 2
      = 1 - ‖phaseCorr σ c t‖ ^ 2 := by
    rw [← hermVar_atomChar hc t, hermVar, hc.expect_atomChar t]
    exact tsum_congr fun n => by rw [mul_pow, Real.sq_sqrt (hc.nonneg n)]
  have hprod : ∀ n : ℕ, (Real.sqrt (normWeight σ c n) * |r n - mean σ c r|)
      * (Real.sqrt (normWeight σ c n) * ‖atomChar t n - phaseCorr σ c t‖)
      = normWeight σ c n * |r n - mean σ c r| * ‖atomChar t n - phaseCorr σ c t‖ := by
    intro n
    have h := Real.mul_self_sqrt (hc.nonneg n)
    calc (Real.sqrt (normWeight σ c n) * |r n - mean σ c r|)
          * (Real.sqrt (normWeight σ c n) * ‖atomChar t n - phaseCorr σ c t‖)
        = (Real.sqrt (normWeight σ c n) * Real.sqrt (normWeight σ c n))
            * (|r n - mean σ c r| * ‖atomChar t n - phaseCorr σ c t‖) := by ring
      _ = normWeight σ c n * |r n - mean σ c r| * ‖atomChar t n - phaseCorr σ c t‖ := by
          rw [h]; ring
  have hnormsum : Summable fun n =>
      ‖((normWeight σ c n : ℝ) : ℂ) * ((r n - mean σ c r : ℝ) : ℂ)
        * (atomChar t n - phaseCorr σ c t)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_
      (hsm.mul_right (1 + ‖phaseCorr σ c t‖))
    intro n
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (hc.nonneg n)]
    nlinarith [norm_atomChar_sub_le σ c t n,
      mul_nonneg (hc.nonneg n) (abs_nonneg (r n - mean σ c r))]
  have hle : ‖phaseResponse σ c (fun n => c n * r n) t‖
      ≤ Real.sqrt (fisherVar σ c r) * Real.sqrt (1 - ‖phaseCorr σ c t‖ ^ 2) := by
    rw [phaseResponse_centered hc hr (mean σ c r) t]
    refine (norm_tsum_le_tsum_norm hnormsum).trans ?_
    have heq : ∀ n : ℕ, ‖((normWeight σ c n : ℝ) : ℂ) * ((r n - mean σ c r : ℝ) : ℂ)
        * (atomChar t n - phaseCorr σ c t)‖
        = (Real.sqrt (normWeight σ c n) * |r n - mean σ c r|)
          * (Real.sqrt (normWeight σ c n) * ‖atomChar t n - phaseCorr σ c t‖) := by
      intro n
      rw [hprod n, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hc.nonneg n)]
    rw [tsum_congr heq, ← hA', ← hB']
    exact ContinuousLinearMap.tsum_mul_le_sqrt_mul_sqrt hA hB
  have hF0 : 0 ≤ fisherVar σ c r := fisherVar_nonneg hc r
  have hH0 : 0 ≤ 1 - ‖phaseCorr σ c t‖ ^ 2 := by
    rw [← hermVar_atomChar hc t]
    exact hermVar_nonneg hc _
  have hsq : (Real.sqrt (fisherVar σ c r) * Real.sqrt (1 - ‖phaseCorr σ c t‖ ^ 2)) ^ 2
      = fisherVar σ c r * (1 - ‖phaseCorr σ c t‖ ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hF0, Real.sq_sqrt hH0]
  have h2 : ‖phaseResponse σ c (fun n => c n * r n) t‖ ^ 2
      ≤ (Real.sqrt (fisherVar σ c r) * Real.sqrt (1 - ‖phaseCorr σ c t‖ ^ 2)) ^ 2 := by
    nlinarith [hle, norm_nonneg (phaseResponse σ c (fun n => c n * r n) t)]
  rw [hsq] at h2
  exact h2

/-- **`(MER.17)`.**  The coarse Fisher-cost bound. -/
theorem phaseResponse_normSq_le_fisherVar {c r : ℕ → ℝ} (hc : IsMarkedState σ c)
    (hr : Summable fun n => normWeight σ c n * |r n|)
    (hr2 : Summable fun n => normWeight σ c n * r n ^ 2) (t : ℝ) :
    ‖phaseResponse σ c (fun n => c n * r n) t‖ ^ 2 ≤ fisherVar σ c r := by
  refine (phaseResponse_normSq_le hc hr hr2 t).trans ?_
  nlinarith [fisherVar_nonneg hc r, sq_nonneg ‖phaseCorr σ c t‖]

/-- **`(MER.17)`, the kernel.**  The quotient Fisher seminorm vanishes exactly on scores that are
constant on the active support of `P_c`. -/
theorem fisherVar_eq_zero_iff {c r : ℕ → ℝ} (hc : IsMarkedState σ c)
    (hFV : Summable fun n => normWeight σ c n * (r n - mean σ c r) ^ 2) :
    fisherVar σ c r = 0 ↔ ∀ n, normWeight σ c n ≠ 0 → r n = mean σ c r := by
  constructor
  · intro h n hn
    have hle : normWeight σ c n * (r n - mean σ c r) ^ 2 ≤ fisherVar σ c r :=
      hFV.le_tsum n fun m _ => mul_nonneg (hc.nonneg m) (sq_nonneg _)
    rw [h] at hle
    have h0 : normWeight σ c n * (r n - mean σ c r) ^ 2 = 0 :=
      le_antisymm hle (mul_nonneg (hc.nonneg n) (sq_nonneg _))
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hn
    · have h2 : r n - mean σ c r = 0 := sq_eq_zero_iff.mp h1
      linarith
  · intro h
    have hz : ∀ n, normWeight σ c n * (r n - mean σ c r) ^ 2 = 0 := by
      intro n
      by_cases hn : normWeight σ c n = 0
      · rw [hn, zero_mul]
      · rw [h n hn, sub_self]
        norm_num
    rw [fisherVar, tsum_congr hz, tsum_zero]

/-! ### Time jets -/

/-- The `k`-th log moment of the phase character against a weight sequence. -/
noncomputable def weightMoment (w : ℕ → ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  ∑' n, ((w n : ℝ) : ℂ) * ((logAtom n : ℂ) ^ k * atomChar t n)

/-- The phase character has time derivative `-i log n` times itself. -/
theorem hasDerivAt_atomChar (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => atomChar s n)
      (-(Complex.I * (logAtom n : ℂ)) * atomChar t n) t := by
  have hpt : ∀ s : ℝ, Complex.exp ((-(Complex.I * (logAtom n : ℂ))) * (s : ℂ))
      = atomChar s n := by
    intro s
    rw [atomChar]
    congr 1
    push_cast
    ring
  have h1 : HasDerivAt (fun s : ℝ => (-(Complex.I * (logAtom n : ℂ))) * (s : ℂ))
      (-(Complex.I * (logAtom n : ℂ))) t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).const_mul (-(Complex.I * (logAtom n : ℂ)))
  have h2 := h1.cexp
  rw [hpt t, funext hpt] at h2
  simpa [mul_comm] using h2

/-- Differentiation under the sum: the time derivative of a log moment raises its order. -/
theorem hasDerivAt_weightMoment {w : ℕ → ℝ}
    (hdom : ∀ k, Summable fun n => |w n| * |logAtom n| ^ k) (k : ℕ) (t : ℝ) :
    HasDerivAt (weightMoment w k) (-Complex.I * weightMoment w (k + 1) t) t := by
  have hg : ∀ (n : ℕ) (s : ℝ),
      HasDerivAt (fun s : ℝ => ((w n : ℝ) : ℂ) * ((logAtom n : ℂ) ^ k * atomChar s n))
        (((w n : ℝ) : ℂ) * ((logAtom n : ℂ) ^ k
          * (-(Complex.I * (logAtom n : ℂ)) * atomChar s n))) s :=
    fun n s => ((hasDerivAt_atomChar n s).const_mul ((logAtom n : ℂ) ^ k)).const_mul _
  have hb : ∀ (n : ℕ) (s : ℝ),
      ‖((w n : ℝ) : ℂ) * ((logAtom n : ℂ) ^ k
        * (-(Complex.I * (logAtom n : ℂ)) * atomChar s n))‖
        ≤ |w n| * |logAtom n| ^ (k + 1) := by
    intro n s
    refine le_of_eq ?_
    simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, norm_atomChar, one_mul, mul_one]
    rw [pow_succ]
  have h0 : Summable fun n => ((w n : ℝ) : ℂ) * ((logAtom n : ℂ) ^ k * atomChar t n) := by
    refine Summable.of_norm_bounded (hdom k) fun n => le_of_eq ?_
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_atomChar, mul_one]
  have hsum : ∑' n, ((w n : ℝ) : ℂ) * ((logAtom n : ℂ) ^ k
      * (-(Complex.I * (logAtom n : ℂ)) * atomChar t n))
      = -Complex.I * weightMoment w (k + 1) t := by
    rw [weightMoment, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [pow_succ]
    ring
  rw [← hsum]
  exact hasDerivAt_tsum (hdom (k + 1)) hg hb h0 t

/-- Every time jet of a linear combination of two log moments is the corresponding higher log
moment, scaled by `(-i)^k`. -/
theorem iteratedDeriv_weightMoment_comb {w v : ℕ → ℝ}
    (hw : ∀ k, Summable fun n => |w n| * |logAtom n| ^ k)
    (hv : ∀ k, Summable fun n => |v n| * |logAtom n| ^ k) (α β : ℂ) (j k : ℕ) :
    ∀ t : ℝ, iteratedDeriv k (fun s => α * weightMoment w j s + β * weightMoment v j s) t
      = (-Complex.I) ^ k
        * (α * weightMoment w (j + k) t + β * weightMoment v (j + k) t) := by
  induction k with
  | zero => intro t; simp
  | succ k ih =>
    intro t
    have hfun : iteratedDeriv k (fun s => α * weightMoment w j s + β * weightMoment v j s)
        = fun s => (-Complex.I) ^ k
            * (α * weightMoment w (j + k) s + β * weightMoment v (j + k) s) := funext ih
    have hd : HasDerivAt (fun s => (-Complex.I) ^ k
          * (α * weightMoment w (j + k) s + β * weightMoment v (j + k) s))
        ((-Complex.I) ^ k * (α * (-Complex.I * weightMoment w (j + (k + 1)) t)
          + β * (-Complex.I * weightMoment v (j + (k + 1)) t))) t :=
      (((hasDerivAt_weightMoment hw (j + k) t).const_mul α).add
        ((hasDerivAt_weightMoment hv (j + k) t).const_mul β)).const_mul _
    rw [iteratedDeriv_succ, hfun, hd.deriv]
    ring

theorem weightMoment_div_totalMass {c : ℕ → ℝ} (k : ℕ) (t : ℝ) :
    weightMoment (mellinWeight σ c) k t / ((totalMass σ c : ℝ) : ℂ)
      = expect σ c (fun n => (logAtom n : ℂ) ^ k * atomChar t n) := by
  rw [weightMoment, expect, div_eq_mul_inv, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [normWeight, div_eq_mul_inv]
  push_cast
  ring

/-- **`(MER.18)`.**  Every time jet of the phase correlation is `(-i)^k` times the `k`-th log
moment of the marked probability. -/
theorem iteratedDeriv_phaseCorr {c : ℕ → ℝ} (hZ : totalMass σ c ≠ 0)
    (hdc : ∀ k, Summable fun n => |mellinWeight σ c n| * |logAtom n| ^ k) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (phaseCorr σ c) t
      = (-Complex.I) ^ k * expect σ c (fun n => (logAtom n : ℂ) ^ k * atomChar t n) := by
  have hZc : ((totalMass σ c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hZ
  have hfun : phaseCorr σ c = fun s =>
      ((totalMass σ c : ℝ) : ℂ)⁻¹ * weightMoment (mellinWeight σ c) 0 s
        + (0 : ℂ) * weightMoment (mellinWeight σ c) 0 s := by
    funext s
    simp only [weightMoment, pow_zero, one_mul, zero_mul, add_zero]
    rw [phaseCorr, div_eq_mul_inv, mul_comm]
  rw [hfun, iteratedDeriv_weightMoment_comb hdc hdc _ _ 0 k t, ← weightMoment_div_totalMass k t]
  simp only [Nat.zero_add, zero_mul, add_zero]
  rw [div_eq_mul_inv, mul_comm (weightMoment (mellinWeight σ c) k t)]

/-- **`(MER.18a)`.**  Every time jet of the phase response is the centered `k`-th log moment,
predicted by the marked reporter and the current jet of the correlation. -/
theorem iteratedDeriv_phaseResponse {c h : ℕ → ℝ} (hZ : totalMass σ c ≠ 0)
    (hdc : ∀ k, Summable fun n => |mellinWeight σ c n| * |logAtom n| ^ k)
    (hdh : ∀ k, Summable fun n => |mellinWeight σ h n| * |logAtom n| ^ k) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (phaseResponse σ c h) t
      = (-Complex.I) ^ k
        * ((weightMoment (mellinWeight σ h) k t
              - ((totalMass σ h : ℝ) : ℂ)
                * expect σ c (fun n => (logAtom n : ℂ) ^ k * atomChar t n))
            / ((totalMass σ c : ℝ) : ℂ)) := by
  have hZc : ((totalMass σ c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hZ
  have hsh : Summable fun n => |mellinWeight σ h n| := by simpa using hdh 0
  have hs1 : Summable fun n => ((mellinWeight σ h n : ℝ) : ℂ) * atomChar t n := by
    refine Summable.of_norm_bounded hsh fun n => le_of_eq ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_atomChar, mul_one]
  have hcomb : ∀ s : ℝ, phaseResponse σ c h s
      = ((totalMass σ c : ℝ) : ℂ)⁻¹ * weightMoment (mellinWeight σ h) 0 s
        + (-((totalMass σ h : ℝ) : ℂ) * (((totalMass σ c : ℝ) : ℂ)⁻¹) ^ 2)
          * weightMoment (mellinWeight σ c) 0 s := by
    intro s
    have hs1' : Summable fun n => ((mellinWeight σ h n : ℝ) : ℂ) * atomChar s n := by
      refine Summable.of_norm_bounded hsh fun n => le_of_eq ?_
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_atomChar, mul_one]
    have hs2 : Summable fun n => ((mellinWeight σ h n : ℝ) : ℂ) := by
      refine Summable.of_norm_bounded hsh fun n => le_of_eq ?_
      simp only [Complex.norm_real, Real.norm_eq_abs]
    have hZh : ∑' n, ((mellinWeight σ h n : ℝ) : ℂ) = ((totalMass σ h : ℝ) : ℂ) := by
      rw [totalMass, Complex.ofReal_tsum]
    have hMh : weightMoment (mellinWeight σ h) 0 s
        = ∑' n, ((mellinWeight σ h n : ℝ) : ℂ) * atomChar s n := by
      rw [weightMoment]
      exact tsum_congr fun n => by rw [pow_zero, one_mul]
    have hMc : phaseCorr σ c s
        = weightMoment (mellinWeight σ c) 0 s * ((totalMass σ c : ℝ) : ℂ)⁻¹ := by
      rw [phaseCorr, weightMoment, div_eq_mul_inv]
      congr 1
      exact tsum_congr fun n => by rw [pow_zero, one_mul]
    have hterm : ∀ n : ℕ, ((mellinWeight σ h n : ℝ) : ℂ) * (atomChar s n - phaseCorr σ c s)
        = ((mellinWeight σ h n : ℝ) : ℂ) * atomChar s n
          - ((mellinWeight σ h n : ℝ) : ℂ) * phaseCorr σ c s := fun n => by ring
    rw [phaseResponse, tsum_congr hterm, hs1'.tsum_sub (hs2.mul_right (phaseCorr σ c s)),
      tsum_mul_right, hZh, ← hMh, hMc]
    field_simp
    ring
  rw [funext hcomb, iteratedDeriv_weightMoment_comb hdh hdc _ _ 0 k t,
    ← weightMoment_div_totalMass k t]
  simp only [Nat.zero_add]
  field_simp
  ring

end MarkedMellin

end HTGeometry.ConstraintMotiveRelativity
