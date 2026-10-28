import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula

/-!
# Logarithmic characters and the arithmetic index formula

A **log-scale** on a group `G` is a homomorphism `ℓ : G →* Multiplicative ℝ`; on the Hecke lattice
`Γ = ℚ_{>0}` it is `u ↦ log u` (`heckeLogScale`). It gives the **logarithmic characters**
`χ_s(u) = e^{s ℓ(u)}`, `s ∈ ℂ` (`logChar`). For `s = ρ − ½` this is `u ↦ u^{ρ−1/2}`, the character
by which a zero `ρ` enters the Hecke orbit kernel. Its reflection is `χ_{−s̄}` (`reflectChar_logChar`),
the character of `1 − ρ̄`, and `|χ_s(u)| = e^{Re s · ℓ(u)}`.

**Separation from small scales** (`exists_separating_of_small`). If `ℓ` takes arbitrarily small
positive values, then any finite set of distinct exponents `s_j` with `Re s_j > 0` is separated by
one element: for `0 < ℓ(u) < 2π / D`, `D` exceeding all `|s_j − s_k|`, the values `e^{s_j ℓ(u)}` are
distinct (equality forces `(s_j − s_k) ℓ(u) ∈ 2πiℤ`), have modulus `> 1`, and the reflected values
have modulus `< 1`.

**Arithmetic index formula** (`negIndex_logChar_pairs_eq`, `negIndex_hecke_pairs_eq`). On such a
group, a positive-definite kernel plus the hyperbolic pairs of `κ` distinct right exponents with
nonzero weights has exactly `κ` negative squares. On `ℚ_{>0}`: a positive-definite part plus the
reflected pairs `ω_j u^{ρ_j−1/2} + ω̄_j u^{1/2−ρ̄_j}` of `κ` distinct points right of the critical line
has negative index exactly `κ`. Off-line zeros are counted by the index one by one, whatever the
weights and whatever positive-definite mass the on-line zeros carry.
-/

open Complex Finset Filter
open scoped ComplexConjugate Real
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G]

/-! ### Logarithmic characters -/

/-- The real scale `ℓ(u)` of an element. -/
def scale (ℓ : G →* Multiplicative ℝ) (u : G) : ℝ := Multiplicative.toAdd (ℓ u)

theorem scale_mul (ℓ : G →* Multiplicative ℝ) (u v : G) :
    scale ℓ (u * v) = scale ℓ u + scale ℓ v := by
  simp only [scale, map_mul, toAdd_mul]

theorem scale_inv (ℓ : G →* Multiplicative ℝ) (u : G) : scale ℓ u⁻¹ = -scale ℓ u := by
  simp only [scale, map_inv, toAdd_inv]

/-- The logarithmic character `u ↦ e^{s ℓ(u)}`. -/
def logChar (ℓ : G →* Multiplicative ℝ) (s : ℂ) : G →* ℂ where
  toFun u := cexp (s * (scale ℓ u : ℂ))
  map_one' := by simp [scale]
  map_mul' u v := by
    rw [scale_mul, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem logChar_apply (ℓ : G →* Multiplicative ℝ) (s : ℂ) (u : G) :
    logChar ℓ s u = cexp (s * (scale ℓ u : ℂ)) := rfl

theorem norm_logChar (ℓ : G →* Multiplicative ℝ) (s : ℂ) (u : G) :
    ‖logChar ℓ s u‖ = Real.exp (s.re * scale ℓ u) := by
  rw [logChar_apply, Complex.norm_exp, Complex.re_mul_ofReal]

/-- The reflection of `χ_s` is `χ_{−s̄}`: for `s = ρ − ½` it is the character of `1 − ρ̄`. -/
theorem reflectChar_logChar (ℓ : G →* Multiplicative ℝ) (s : ℂ) :
    reflectChar (logChar ℓ s) = logChar ℓ (-conj s) := by
  ext u
  rw [reflectChar_apply, logChar_apply, logChar_apply, ← Complex.exp_conj, scale_inv,
    Complex.ofReal_neg, map_mul, map_neg, Complex.conj_ofReal]
  ring_nf

/-- Equal exponentials at a short scale have equal exponents. -/
theorem eq_of_cexp_mul_eq {a b : ℂ} {L : ℝ} (hL : 0 < L) (hab : ‖a - b‖ * L < 2 * π)
    (h : cexp (a * L) = cexp (b * L)) : a = b := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hd : (a - b) * L = n * (2 * π * I) := by rw [sub_mul, hn]; ring
  rcases eq_or_ne n 0 with rfl | hn0
  · simp only [Int.cast_zero, zero_mul, mul_eq_zero, Complex.ofReal_eq_zero, hL.ne', or_false,
      sub_eq_zero] at hd
    exact hd
  · exfalso
    have hnorm := congrArg norm hd
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hL.le,
      Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_intCast] at hnorm
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
    nlinarith [Real.pi_pos]

/-- **Separation from small scales.** If `ℓ` takes arbitrarily small positive values, distinct
exponents with positive real part are separated by one element. -/
theorem exists_separating_of_small {κ : ℕ} (ℓ : G →* Multiplicative ℝ)
    (hℓ : ∀ ε : ℝ, 0 < ε → ∃ u, 0 < scale ℓ u ∧ scale ℓ u < ε)
    (s : Fin κ → ℂ) (hs : Function.Injective s) (hre : ∀ j, 0 < (s j).re) :
    ∃ u, (∀ j, ‖logChar ℓ (s j) u‖ ≠ 1) ∧
      Function.Injective (nodes (fun j => logChar ℓ (s j)) u) := by
  set D : ℝ := ∑ j, ∑ k, ‖s j - s k‖ + 1
  have hD : 0 < D := by positivity
  have hDle : ∀ j k, ‖s j - s k‖ < D := fun j k => by
    have := single_le_sum (f := fun k => ‖s j - s k‖) (fun _ _ => norm_nonneg _) (mem_univ k)
    have := this.trans (single_le_sum (f := fun j => ∑ k, ‖s j - s k‖)
      (fun _ _ => sum_nonneg fun _ _ => norm_nonneg _) (mem_univ j))
    linarith
  obtain ⟨u, hu0, huε⟩ := hℓ (2 * π / D) (by positivity)
  set L := scale ℓ u
  have hshort : ∀ a b : ℂ, ‖a - b‖ < D → ‖a - b‖ * L < 2 * π := fun a b h => by
    calc ‖a - b‖ * L ≤ D * L := by gcongr
      _ < D * (2 * π / D) := by gcongr
      _ = 2 * π := by field_simp
  have hgt : ∀ j, 1 < ‖logChar ℓ (s j) u‖ := fun j => by
    rw [norm_logChar]; exact Real.one_lt_exp_iff.mpr (mul_pos (hre j) hu0)
  have hlt : ∀ j, ‖reflectChar (logChar ℓ (s j)) u‖ < 1 := fun j => by
    rw [norm_reflectChar]; exact inv_lt_one_of_one_lt₀ (hgt j)
  refine ⟨u, fun j => (hgt j).ne', ?_⟩
  rintro (j | j) (k | k) h <;> simp only [nodes, Sum.elim_inl, Sum.elim_inr] at h
  · rw [logChar_apply, logChar_apply] at h
    exact congrArg Sum.inl (hs (eq_of_cexp_mul_eq hu0 (hshort _ _ (hDle j k)) h))
  · exact absurd (congrArg norm h) (ne_of_gt ((hlt k).trans (hgt j)))
  · exact absurd (congrArg norm h) (ne_of_lt ((hlt j).trans (hgt k)))
  · rw [reflectChar_logChar, reflectChar_logChar, logChar_apply, logChar_apply] at h
    have := eq_of_cexp_mul_eq hu0 (hshort _ _ (by
      rw [show -conj (s j) - -conj (s k) = -conj (s j - s k) by rw [map_sub]; ring, norm_neg,
        Complex.norm_conj]
      exact hDle j k)) h
    exact congrArg Sum.inr (hs (by simpa using congrArg (fun z => conj (-z)) this))

/-- **Arithmetic index formula on a group with small scales.** -/
theorem negIndex_logChar_pairs_eq {κ : ℕ} (ℓ : G →* Multiplicative ℝ)
    (hℓ : ∀ ε : ℝ, 0 < ε → ∃ u, 0 < scale ℓ u ∧ scale ℓ u < ε)
    {p : G → ℂ} (hp : IsPosDefKernel p) (s : Fin κ → ℂ) (hs : Function.Injective s)
    (hre : ∀ j, 0 < (s j).re) (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) :
    negIndex (fun g => p g + ∑ j, pairKernel (logChar ℓ (s j)) (ω j) g) = κ := by
  obtain ⟨u, hne, hsep⟩ := exists_separating_of_small ℓ hℓ s hs hre
  exact negIndex_add_sum_pairKernel_eq hp _ ω hω u hne hsep

/-! ### The Hecke lattice `ℚ_{>0}` -/

/-- The Hecke lattice: the multiplicative group of positive rationals. -/
abbrev HeckeLattice := {q : ℚ // 0 < q}

/-- The logarithm `u ↦ log u` on the Hecke lattice. -/
def heckeLogScale : HeckeLattice →* Multiplicative ℝ where
  toFun u := Multiplicative.ofAdd (Real.log ((u : ℚ) : ℝ))
  map_one' := by simp
  map_mul' u v := by
    rw [← ofAdd_add, show (((u * v : HeckeLattice) : ℚ) : ℝ) = ((u : ℚ) : ℝ) * ((v : ℚ) : ℝ) by
      exact_mod_cast rfl,
      Real.log_mul (by exact_mod_cast u.2.ne') (by exact_mod_cast v.2.ne')]

theorem scale_heckeLogScale (u : HeckeLattice) :
    scale heckeLogScale u = Real.log ((u : ℚ) : ℝ) := rfl

/-- The Hecke lattice has arbitrarily small positive scales: `1 < q < e^ε`. -/
theorem heckeLogScale_small (ε : ℝ) (hε : 0 < ε) :
    ∃ u : HeckeLattice, 0 < scale heckeLogScale u ∧
      scale heckeLogScale u < ε := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (Real.one_lt_exp_iff.mpr hε)
  have hq0 : (0 : ℝ) < q := one_pos.trans hq1
  refine ⟨⟨q, by exact_mod_cast hq0⟩, ?_, ?_⟩
  · rw [scale_heckeLogScale]; exact Real.log_pos hq1
  · rw [scale_heckeLogScale, Real.log_lt_iff_lt_exp hq0]; exact hq2

/-- The character `u ↦ u^{ρ − 1/2}` of a zero `ρ` on the Hecke lattice. -/
abbrev zeroChar (ρ : ℂ) : HeckeLattice →* ℂ := logChar heckeLogScale (ρ - 1 / 2)

/-- **The arithmetic Krein–Langer index formula on `ℚ_{>0}`.** A positive-definite kernel plus the
reflected pairs of `κ` distinct points right of the critical line, with nonzero weights, has exactly
`κ` negative squares. -/
theorem negIndex_hecke_pairs_eq {κ : ℕ} {p : HeckeLattice → ℂ} (hp : IsPosDefKernel p)
    (ρ : Fin κ → ℂ) (hρ : Function.Injective ρ) (hre : ∀ j, 1 / 2 < (ρ j).re) (ω : Fin κ → ℂ)
    (hω : ∀ j, ω j ≠ 0) :
    negIndex (fun g => p g + ∑ j, pairKernel (zeroChar (ρ j)) (ω j) g) = κ :=
  negIndex_logChar_pairs_eq heckeLogScale heckeLogScale_small hp (fun j => ρ j - 1 / 2)
    (fun j k h => hρ (sub_left_injective h)) (fun j => by rw [Complex.sub_re]; norm_num; linarith [hre j]) ω hω

end GaloisForLFunctions.HeckeKreinToeplitz
