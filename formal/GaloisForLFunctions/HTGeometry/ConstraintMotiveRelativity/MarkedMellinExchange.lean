import Mathlib

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

end MarkedMellin

end HTGeometry.ConstraintMotiveRelativity
