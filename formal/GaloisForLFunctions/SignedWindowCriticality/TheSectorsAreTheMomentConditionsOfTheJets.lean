import GaloisForLFunctions.SignedWindowCriticality.TheContinuumCanonicalSystemSplitsIntoTheParitySectors
import GaloisForLFunctions.HTGeometry.StieltjesSemidefiniteCriterion

/-!
# The parity sectors are the moment conditions of the jets

For an even smooth bump `φ` put `s_k = W(φ^{(k)})` (`jetEnergy`). Translation invariance makes
`d/dx` skew for `W`, so for a polynomial `p` the moment functional `L` of `(s_k)` is Weil's form
on the jet polynomials of `φ`:

  `L(p²) = W(p(−D²)φ)` and `L(x·p²) = W((p(−D²)φ)')`

(`momentInner_jetEnergy_eq`, `momentFunctional_X_mul_sq_jetEnergy_eq`). For an even bump
`p(−D²)φ` is an even test and `(p(−D²)φ)'` an odd one, and every odd test of a symmetric window is
the derivative of an even test of the same window (`exists_even_antideriv`). Hence, on `[−a, a]`:

* **the even sector is the Hamburger condition** (`even_nonneg_iff_hamburger`): it is nonnegative
  iff the jet energies of every even smooth bump are the moments of a finite positive measure on
  the line;
* **the odd sector is the shifted Hamburger condition** (`odd_nonneg_iff_shiftedHamburger`): it is
  nonnegative iff the shifted jet energies `s_{k+1}` are;
* **the window is the Stieltjes condition** (`window_nonneg_iff_stieltjes`): it is nonnegative iff
  the jet energies of every even smooth bump are the moments of a finite positive measure on
  `[0, ∞)`.

For a nonzero bump the Hankel forms are positive definite (`positiveMomentForm_jetEnergy`,
`positiveMomentForm_shiftedJetEnergy`). The representing measures are built from the sequence
alone (the corpus' Hamburger and Stieltjes existence theorems); no zero of `ζ` enters.

Reading `x = ξ²` for the frequency `ξ`: a nonnegative window gives every even bump a **spectral
measure on `[0, ∞)`**, the measure the zeros it sees would carry if they were real. The even sector
makes the weights positive on the whole `x`-line, which still allows atoms at `x < 0`, i.e. at
imaginary `ξ` — the place of zeros on the real axis of `s` and of the pole (`x = −¼`); the odd
sector removes the negative half-line.
-/

open MeasureTheory Set Filter Topology Polynomial
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis DimensionZeroGeometryOfSpecZ
open GrowingWindowsOfSpecZ

variable {φ : ℝ → ℝ}

/-- The **jet energies** `s_k = W(φ^{(k)})` of a bump. -/
def jetEnergy (φ : ℝ → ℝ) (k : ℕ) : ℝ := weilQuad (iteratedDeriv k φ)

theorem weilPair_self_iteratedDeriv_eq (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (m : ℕ) :
    weilPair φ (iteratedDeriv (2 * m) φ) = (-1) ^ m * jetEnergy φ m := by
  have h := weilPair_iteratedDeriv_eq hφ hφc m m
  have h1 : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  unfold jetEnergy
  rw [show weilQuad (iteratedDeriv m φ) = weilPair (iteratedDeriv m φ) (iteratedDeriv m φ) from rfl,
    h, show m + m = 2 * m by ring, ← mul_assoc, h1, one_mul]

/-- `W(φ^{(2i)}, φ^{(2j)}) = (−1)^{i+j} s_{i+j}`. -/
theorem weilPair_evenJets (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (i j : ℕ) :
    weilPair (iteratedDeriv (2 * i) φ) (iteratedDeriv (2 * j) φ) =
      (-1) ^ (i + j) * jetEnergy φ (i + j) := by
  rw [weilPair_iteratedDeriv_eq hφ hφc (2 * i) (2 * j), show 2 * i + 2 * j = 2 * (i + j) by ring,
    weilPair_self_iteratedDeriv_eq hφ hφc, pow_mul, neg_one_sq, one_pow, one_mul]

/-- `W(φ^{(2i+1)}, φ^{(2j+1)}) = (−1)^{i+j} s_{i+j+1}`. -/
theorem weilPair_oddJets (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (i j : ℕ) :
    weilPair (iteratedDeriv (2 * i + 1) φ) (iteratedDeriv (2 * j + 1) φ) =
      (-1) ^ (i + j) * jetEnergy φ (i + j + 1) := by
  rw [weilPair_iteratedDeriv_eq hφ hφc (2 * i + 1) (2 * j + 1),
    show 2 * i + 1 + (2 * j + 1) = 2 * (i + j + 1) by ring, weilPair_self_iteratedDeriv_eq hφ hφc,
    Odd.neg_one_pow ⟨i, rfl⟩, pow_succ]
  ring

/-! ### The jet polynomials `p(−D²)φ` and `(p(−D²)φ)'` -/

/-- `p(−D²)φ` for `p = Σ vᵢXⁱ`. -/
def evenComb (φ : ℝ → ℝ) {n : ℕ} (v : Fin n → ℝ) : ℝ → ℝ :=
  ∑ i : Fin n, ((-1) ^ (i : ℕ) * v i) • iteratedDeriv (2 * (i : ℕ)) φ

/-- `(p(−D²)φ)'` for `p = Σ vᵢXⁱ`. -/
def oddComb (φ : ℝ → ℝ) {n : ℕ} (v : Fin n → ℝ) : ℝ → ℝ :=
  ∑ i : Fin n, ((-1) ^ (i : ℕ) * v i) • iteratedDeriv (2 * (i : ℕ) + 1) φ

theorem jetComb_apply {n : ℕ} (c : Fin n → ℝ) (d : Fin n → ℕ) (x : ℝ) :
    (∑ i, c i • iteratedDeriv (d i) φ) x = ∑ i, c i * iteratedDeriv (d i) φ x := by
  simp [Finset.sum_apply]

theorem contDiff_jetComb (hφ : ContDiff ℝ ∞ φ) {n : ℕ} (c : Fin n → ℝ) (d : Fin n → ℕ) :
    ContDiff ℝ ∞ (∑ i, c i • iteratedDeriv (d i) φ) := by
  have e : (∑ i, c i • iteratedDeriv (d i) φ) = fun x => ∑ i, c i * iteratedDeriv (d i) φ x :=
    funext (jetComb_apply c d)
  rw [e]
  exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_iteratedDeriv_of_smooth hφ _)

theorem supportedIn_jetComb {a : ℝ} (hφa : SupportedIn a φ) {n : ℕ} (c : Fin n → ℝ)
    (d : Fin n → ℕ) : SupportedIn a (∑ i, c i • iteratedDeriv (d i) φ) := fun u hu => by
  rw [jetComb_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [iteratedDeriv_supportedIn hφa _ u hu, mul_zero]

theorem contDiff_evenComb (hφ : ContDiff ℝ ∞ φ) {n : ℕ} (v : Fin n → ℝ) :
    ContDiff ℝ ∞ (evenComb φ v) := contDiff_jetComb hφ _ _

theorem contDiff_oddComb (hφ : ContDiff ℝ ∞ φ) {n : ℕ} (v : Fin n → ℝ) :
    ContDiff ℝ ∞ (oddComb φ v) := contDiff_jetComb hφ _ _

theorem supportedIn_evenComb {a : ℝ} (hφa : SupportedIn a φ) {n : ℕ} (v : Fin n → ℝ) :
    SupportedIn a (evenComb φ v) := supportedIn_jetComb hφa _ _

theorem supportedIn_oddComb {a : ℝ} (hφa : SupportedIn a φ) {n : ℕ} (v : Fin n → ℝ) :
    SupportedIn a (oddComb φ v) := supportedIn_jetComb hφa _ _

theorem evenComb_even (hφe : ∀ x, φ (-x) = φ x) {n : ℕ} (v : Fin n → ℝ) (x : ℝ) :
    evenComb φ v (-x) = evenComb φ v x := by
  simp only [evenComb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_parity hφe, pow_mul, neg_one_sq, one_pow, one_mul]

theorem oddComb_odd (hφe : ∀ x, φ (-x) = φ x) {n : ℕ} (v : Fin n → ℝ) (x : ℝ) :
    oddComb φ v (-x) = -oddComb φ v x := by
  simp only [oddComb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_parity hφe, Odd.neg_one_pow ⟨i, rfl⟩]
  ring

/-- `W(p(−D²)φ) = Σᵢⱼ vᵢvⱼ s_{i+j}`. -/
theorem weilQuad_evenComb (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) {n : ℕ}
    (v : Fin n → ℝ) :
    weilQuad (evenComb φ v) = ∑ i, ∑ j, v i * v j * jetEnergy φ ((i : ℕ) + (j : ℕ)) := by
  have h := weilPair_sum_smul_sum_smul (f := fun i : Fin n => iteratedDeriv (2 * (i : ℕ)) φ)
    (fun i => iteratedDeriv_mem_realTests hφ hφc (2 * i)) (fun i => (-1) ^ (i : ℕ) * v i)
  show weilPair (evenComb φ v) (evenComb φ v) = _
  unfold evenComb
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weilPair_evenJets hφ hφc]
  have hs : ((-1 : ℝ) ^ (i : ℕ)) * (-1) ^ ((i : ℕ) + j) * (-1) ^ (j : ℕ) = 1 := by
    rw [← pow_add, ← pow_add]; exact Even.neg_one_pow ⟨i + j, by ring⟩
  linear_combination (v i * v j * jetEnergy φ ((i : ℕ) + (j : ℕ))) * hs

/-- `W((p(−D²)φ)') = Σᵢⱼ vᵢvⱼ s_{i+j+1}`. -/
theorem weilQuad_oddComb (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) {n : ℕ}
    (v : Fin n → ℝ) :
    weilQuad (oddComb φ v) = ∑ i, ∑ j, v i * v j * jetEnergy φ ((i : ℕ) + (j : ℕ) + 1) := by
  have h := weilPair_sum_smul_sum_smul (f := fun i : Fin n => iteratedDeriv (2 * (i : ℕ) + 1) φ)
    (fun i => iteratedDeriv_mem_realTests hφ hφc (2 * i + 1)) (fun i => (-1) ^ (i : ℕ) * v i)
  show weilPair (oddComb φ v) (oddComb φ v) = _
  unfold oddComb
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weilPair_oddJets hφ hφc]
  have hs : ((-1 : ℝ) ^ (i : ℕ)) * (-1) ^ ((i : ℕ) + j) * (-1) ^ (j : ℕ) = 1 := by
    rw [← pow_add, ← pow_add]; exact Even.neg_one_pow ⟨i + j, by ring⟩
  linear_combination (v i * v j * jetEnergy φ ((i : ℕ) + (j : ℕ) + 1)) * hs

/-! ### The moment functional of the jet energies is Weil's form on jet polynomials -/

theorem poly_eq_sum_coeff (p : ℝ[X]) :
    p = ∑ i : Fin (p.natDegree + 1), p.coeff i • (X : ℝ[X]) ^ (i : ℕ) := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  rw [Finset.sum_range]
  simp only [C_mul']

/-- **`L(p²) = W(p(−D²)φ)`**: the Hankel form of the jet energies is Weil's form on the even
test `p(−D²)φ`. -/
theorem momentInner_jetEnergy_eq (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (p : ℝ[X]) :
    _root_.HTGeometry.momentInner (jetEnergy φ) p p =
      weilQuad (evenComb φ fun i : Fin (p.natDegree + 1) => p.coeff i) := by
  rw [_root_.HTGeometry.momentInner_self]
  conv_lhs => rw [poly_eq_sum_coeff p]
  rw [_root_.HTGeometry.momentFunctional_sq_eq_hankelForm, weilQuad_evenComb hφ hφc]

/-- **`L(x·p²) = W((p(−D²)φ)')`**: the shifted Hankel form is Weil's form on the odd test
`(p(−D²)φ)'`. -/
theorem momentFunctional_X_mul_sq_jetEnergy_eq (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (p : ℝ[X]) :
    _root_.HTGeometry.momentFunctional (jetEnergy φ) (X * p ^ 2) =
      weilQuad (oddComb φ fun i : Fin (p.natDegree + 1) => p.coeff i) := by
  conv_lhs => rw [poly_eq_sum_coeff p]
  rw [_root_.HTGeometry.momentFunctional_X_mul_sq_eq_shiftedHankel, weilQuad_oddComb hφ hφc]

/-- The Hankel form of the shifted jet energies `k ↦ s_{k+1}` is the shifted form. -/
theorem momentInner_shiftedJetEnergy_eq (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (p : ℝ[X]) :
    _root_.HTGeometry.momentInner (fun k => jetEnergy φ (k + 1)) p p =
      weilQuad (oddComb φ fun i : Fin (p.natDegree + 1) => p.coeff i) := by
  rw [_root_.HTGeometry.momentInner_self]
  conv_lhs => rw [poly_eq_sum_coeff p]
  rw [_root_.HTGeometry.momentFunctional_sq_eq_hankelForm, weilQuad_oddComb hφ hφc]

/-! ### Nondegeneracy of the jet polynomials -/

theorem eq_zero_of_sum_smul_evenJets (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : φ ≠ 0) (n : ℕ) (x : Fin n → ℝ) (h : ∑ i, x i • iteratedDeriv (2 * i) φ = 0) :
    x = 0 := by
  have e : (2 * n + 1) / 2 = n := by omega
  have h' := (eq_zero_of_sum_smul_parityJets hφ hφc hφ0 (2 * n) (fun p => x (finCongr e p)) 0
    (by
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
      rw [← h]
      exact Fintype.sum_equiv (finCongr e) _ _ fun p => rfl)).1
  funext i
  simpa using congrFun h' ((finCongr e).symm i)

theorem eq_zero_of_sum_smul_oddJets (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : φ ≠ 0) (n : ℕ) (x : Fin n → ℝ) (h : ∑ i, x i • iteratedDeriv (2 * i + 1) φ = 0) :
    x = 0 := by
  have e : 2 * n / 2 = n := by omega
  have h' := (eq_zero_of_sum_smul_parityJets hφ hφc hφ0 (2 * n) 0 (fun p => x (finCongr e p))
    (by
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
      rw [← h]
      exact Fintype.sum_equiv (finCongr e) _ _ fun p => rfl)).2
  funext i
  simpa using congrFun h' ((finCongr e).symm i)

theorem eq_zero_of_coeffs_eq_zero (p : ℝ[X])
    (h : (fun i : Fin (p.natDegree + 1) => (-1) ^ (i : ℕ) * p.coeff i) = 0) : p = 0 := by
  have hlead := congrFun h ⟨p.natDegree, Nat.lt_succ_self _⟩
  have h1 : ((-1 : ℝ) ^ p.natDegree) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact Polynomial.leadingCoeff_eq_zero.mp ((mul_eq_zero.mp hlead).resolve_left h1)

/-! ### Each sector is a moment condition on the jets of even bumps -/

variable {a : ℝ}

/-- **The even sector makes the jet energies a Hamburger sequence**: for a nonzero even smooth
bump on a window whose even sector is nonnegative, `L(p²) = W(p(−D²)φ) > 0` for every `p ≠ 0`. -/
theorem positiveMomentForm_jetEnergy
    (hne : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = G x) → 0 ≤ weilQuad G)
    (hφ : ContDiff ℝ ∞ φ) (hφa : SupportedIn a φ) (hφe : ∀ x, φ (-x) = φ x) (hφ0 : φ ≠ 0) :
    _root_.HTGeometry.PositiveMomentForm (jetEnergy φ) := by
  have hφc := hasCompactSupport_of_supportedIn' hφa
  refine ⟨fun p hp => ?_⟩
  rw [momentInner_jetEnergy_eq hφ hφc]
  refine weilQuad_pos_of_sector_nonneg 1 (Or.inl rfl)
    (fun G hG hGa hGp => hne G hG hGa fun x => by rw [hGp, one_mul])
    (contDiff_evenComb hφ _) (supportedIn_evenComb hφa _)
    (fun x => by rw [evenComb_even hφe, one_mul]) fun h0 => hp ?_
  exact eq_zero_of_coeffs_eq_zero p (eq_zero_of_sum_smul_evenJets hφ hφc hφ0 _ _ h0)

/-- **The odd sector makes the shifted jet energies a Hamburger sequence**: for a nonzero even
smooth bump on a window whose odd sector is nonnegative, `L(x·p²) = W((p(−D²)φ)') > 0` for every
`p ≠ 0`. -/
theorem positiveMomentForm_shiftedJetEnergy
    (hno : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = -G x) →
      0 ≤ weilQuad G)
    (hφ : ContDiff ℝ ∞ φ) (hφa : SupportedIn a φ) (hφe : ∀ x, φ (-x) = φ x) (hφ0 : φ ≠ 0) :
    _root_.HTGeometry.PositiveMomentForm (fun k => jetEnergy φ (k + 1)) := by
  have hφc := hasCompactSupport_of_supportedIn' hφa
  refine ⟨fun p hp => ?_⟩
  rw [momentInner_shiftedJetEnergy_eq hφ hφc]
  refine weilQuad_pos_of_sector_nonneg (-1) (Or.inr rfl)
    (fun G hG hGa hGp => hno G hG hGa fun x => by rw [hGp, neg_one_mul])
    (contDiff_oddComb hφ _) (supportedIn_oddComb hφa _)
    (fun x => by rw [oddComb_odd hφe, neg_one_mul]) fun h0 => hp ?_
  exact eq_zero_of_coeffs_eq_zero p (eq_zero_of_sum_smul_oddJets hφ hφc hφ0 _ _ h0)

theorem iteratedDeriv_zero_fun (k : ℕ) : iteratedDeriv k (0 : ℝ → ℝ) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact deriv_const x 0

theorem weilQuad_zero : weilQuad (0 : ℝ → ℝ) = 0 := by
  have h := weilQuad_add (realTests.zero_mem) (realTests.zero_mem)
  rw [add_zero] at h
  have : weilQuad (0 : ℝ → ℝ) = weilPair 0 0 := rfl
  linarith

theorem jetEnergy_zero_fun (k : ℕ) : jetEnergy 0 k = 0 := by
  rw [jetEnergy, iteratedDeriv_zero_fun, weilQuad_zero]

/-- On an even-nonnegative window every even bump has a **Hamburger spectral measure**: a finite
positive measure on the line with `∫ x^k dν = W(φ^{(k)})`. -/
theorem exists_hamburgerMeasure_of_even_nonneg
    (hne : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = G x) → 0 ≤ weilQuad G)
    (hφ : ContDiff ℝ ∞ φ) (hφa : SupportedIn a φ) (hφe : ∀ x, φ (-x) = φ x) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments (jetEnergy φ) ν := by
  by_cases hφ0 : φ = 0
  · subst hφ0
    exact ⟨0, inferInstance, fun k => ⟨integrable_zero_measure, by
      rw [jetEnergy_zero_fun, integral_zero_measure]⟩⟩
  · exact _root_.HTGeometry.exists_finiteMeasure_hasHamburgerMoments
      (positiveMomentForm_jetEnergy hne hφ hφa hφe hφ0)

/-- On an odd-nonnegative window the shifted jet energies `s_{k+1}` of every even bump have a
Hamburger spectral measure. -/
theorem exists_shiftedHamburgerMeasure_of_odd_nonneg
    (hno : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = -G x) →
      0 ≤ weilQuad G)
    (hφ : ContDiff ℝ ∞ φ) (hφa : SupportedIn a φ) (hφe : ∀ x, φ (-x) = φ x) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments (fun k => jetEnergy φ (k + 1)) ν := by
  by_cases hφ0 : φ = 0
  · subst hφ0
    exact ⟨0, inferInstance, fun k => ⟨integrable_zero_measure, by
      simp only [jetEnergy_zero_fun, integral_zero_measure]⟩⟩
  · exact _root_.HTGeometry.exists_finiteMeasure_hasHamburgerMoments
      (positiveMomentForm_shiftedJetEnergy hno hφ hφa hφe hφ0)

/-- On a window with both sectors nonnegative every even bump has a **Stieltjes spectral
measure**: a finite positive measure on `[0, ∞)` with `∫ x^k dν = W(φ^{(k)})`. -/
theorem exists_stieltjesMeasure_of_sectors_nonneg
    (hne : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = G x) → 0 ≤ weilQuad G)
    (hno : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = -G x) →
      0 ≤ weilQuad G)
    (hφ : ContDiff ℝ ∞ φ) (hφa : SupportedIn a φ) (hφe : ∀ x, φ (-x) = φ x) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ _root_.HTGeometry.HasStieltjesMoments (jetEnergy φ) ν := by
  have hφc := hasCompactSupport_of_supportedIn' hφa
  refine _root_.HTGeometry.exists_finiteMeasure_hasStieltjesMoments_semidefinite (fun p => ?_)
    (fun p => ?_)
  · rw [momentInner_jetEnergy_eq hφ hφc]
    exact hne _ (contDiff_evenComb hφ _) (supportedIn_evenComb hφa _) (evenComb_even hφe _)
  · rw [momentFunctional_X_mul_sq_jetEnergy_eq hφ hφc]
    exact hno _ (contDiff_oddComb hφ _) (supportedIn_oddComb hφa _) (oddComb_odd hφe _)

/-! ### Every odd test is the derivative of an even one -/

/-- An odd smooth test on `[−a, a]` is the derivative of the even smooth test
`x ↦ ∫_{−a}^x G` on `[−a, a]`. -/
theorem exists_even_antideriv {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (hGa : SupportedIn a G)
    (hGo : ∀ x, G (-x) = -G x) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ SupportedIn a ψ ∧ (∀ x, ψ (-x) = ψ x) ∧ deriv ψ = G := by
  have hGc : Continuous G := hG.continuous
  set ψ : ℝ → ℝ := fun x => ∫ t in (-a)..x, G t with hψ
  have hderiv : deriv ψ = G := funext fun x => Continuous.deriv_integral G hGc (-a) x
  have hdiff : Differentiable ℝ ψ := fun x =>
    (hGc.integral_hasStrictDerivAt (-a) x).hasDerivAt.differentiableAt
  have hsmooth : ContDiff ℝ ∞ ψ := contDiff_infty_iff_deriv.mpr ⟨hdiff, hderiv ▸ hG⟩
  have htot : ∫ t in (-a)..a, G t = 0 := by
    have h1 := intervalIntegral.integral_comp_neg (f := G) (a := -a) (b := a)
    rw [neg_neg] at h1
    simp only [hGo, intervalIntegral.integral_neg] at h1
    linarith
  have heven : ∀ x, ψ (-x) = ψ x := by
    intro x
    simp only [hψ]
    have h1 := intervalIntegral.integral_comp_neg (f := G) (a := x) (b := a)
    simp only [hGo, intervalIntegral.integral_neg] at h1
    have h2 := intervalIntegral.integral_add_adjacent_intervals (hGc.intervalIntegrable (μ := volume) (-a) x)
      (hGc.intervalIntegrable (μ := volume) x a)
    rw [htot] at h2
    linarith
  have hpos : ∀ u, a < u → ψ u = 0 := by
    intro u hu
    simp only [hψ]
    have h2 := intervalIntegral.integral_add_adjacent_intervals (hGc.intervalIntegrable (μ := volume) (-a) a)
      (hGc.intervalIntegrable (μ := volume) a u)
    rw [htot, zero_add] at h2
    rw [← h2, intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_,
      intervalIntegral.integral_zero]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hu.le] at ht
    exact hGa t (lt_of_lt_of_le ht.1 (le_abs_self t))
  refine ⟨ψ, hsmooth, fun u hu => ?_, heven, hderiv⟩
  rcases lt_or_ge 0 u with h0 | h0
  · exact hpos u (by rwa [abs_of_pos h0] at hu)
  · rw [← heven]
    exact hpos (-u) (by rwa [abs_of_nonpos h0] at hu)

/-! ### The converses: the moment conditions are the sectors -/

theorem even_nonneg_of_hamburger
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → SupportedIn a φ → (∀ x, φ (-x) = φ x) →
      ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
        GaloisForLFunctions.HTGeometry.HasHamburgerMoments (jetEnergy φ) ν)
    (G : ℝ → ℝ) (hG : ContDiff ℝ ∞ G) (hGa : SupportedIn a G) (hGe : ∀ x, G (-x) = G x) :
    0 ≤ weilQuad G := by
  obtain ⟨ν, -, hm⟩ := h G hG hGa hGe
  have h0 := (hm 0).2
  simp only [pow_zero, jetEnergy, iteratedDeriv_zero] at h0
  rw [← h0]
  exact integral_nonneg fun _ => zero_le_one

theorem odd_nonneg_of_shiftedHamburger
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → SupportedIn a φ → (∀ x, φ (-x) = φ x) →
      ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
        GaloisForLFunctions.HTGeometry.HasHamburgerMoments (fun k => jetEnergy φ (k + 1)) ν)
    (G : ℝ → ℝ) (hG : ContDiff ℝ ∞ G) (hGa : SupportedIn a G) (hGo : ∀ x, G (-x) = -G x) :
    0 ≤ weilQuad G := by
  obtain ⟨ψ, hψ, hψa, hψe, hψG⟩ := exists_even_antideriv hG hGa hGo
  obtain ⟨ν, -, hm⟩ := h ψ hψ hψa hψe
  have h0 := (hm 0).2
  simp only [pow_zero, zero_add, jetEnergy, iteratedDeriv_one, hψG] at h0
  rw [← h0]
  exact integral_nonneg fun _ => zero_le_one

/-- A window is nonnegative as soon as both of its parity sectors are. -/
theorem window_nonneg_of_sectors
    (hne : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = G x) → 0 ≤ weilQuad G)
    (hno : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = -G x) →
      0 ≤ weilQuad G)
    (G : ℝ → ℝ) (hG : ContDiff ℝ ∞ G) (hGa : SupportedIn a G) : 0 ≤ weilQuad G := by
  set Ge := fun x => (G x + G (-x)) / 2
  set Go := fun x => (G x - G (-x)) / 2
  have hGeq : G = Ge + Go := by funext x; simp only [Ge, Go, Pi.add_apply]; ring
  have hGer := smooth_mem_realTests (evenPart_smooth hG) (supportedIn_evenPart hGa)
  have hGor := smooth_mem_realTests (oddPart_smooth hG) (supportedIn_oddPart hGa)
  have hGe : ∀ x, Ge (-x) = Ge x := fun x => by simp only [Ge, neg_neg]; ring
  have hGo : ∀ x, Go (-x) = -Go x := fun x => by simp only [Go, neg_neg]; ring
  rw [hGeq, weilQuad_add hGer hGor, weilPair_comm, weilPair_odd_even hGor hGer hGo hGe]
  have h1 := hne Ge (evenPart_smooth hG) (supportedIn_evenPart hGa) hGe
  have h2 := hno Go (oddPart_smooth hG) (supportedIn_oddPart hGa) hGo
  linarith

/-! ### The dictionary -/

/-- **The even sector is the Hamburger condition on the jets**: the even sector of `[−a, a]` is
nonnegative iff the jet energies of every even smooth bump on it are the moments of a finite
positive measure on the line. -/
theorem even_nonneg_iff_hamburger :
    (∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = G x) → 0 ≤ weilQuad G) ↔
      ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → SupportedIn a φ → (∀ x, φ (-x) = φ x) →
        ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
          GaloisForLFunctions.HTGeometry.HasHamburgerMoments (jetEnergy φ) ν :=
  ⟨fun hne _ hφ hφa hφe => exists_hamburgerMeasure_of_even_nonneg hne hφ hφa hφe,
    even_nonneg_of_hamburger⟩

/-- **The odd sector is the shifted Hamburger condition on the jets**: the odd sector of `[−a, a]`
is nonnegative iff the shifted jet energies `s_{k+1}` of every even smooth bump on it are the
moments of a finite positive measure on the line. -/
theorem odd_nonneg_iff_shiftedHamburger :
    (∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = -G x) → 0 ≤ weilQuad G) ↔
      ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → SupportedIn a φ → (∀ x, φ (-x) = φ x) →
        ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
          GaloisForLFunctions.HTGeometry.HasHamburgerMoments (fun k => jetEnergy φ (k + 1)) ν :=
  ⟨fun hno _ hφ hφa hφe => exists_shiftedHamburgerMeasure_of_odd_nonneg hno hφ hφa hφe,
    odd_nonneg_of_shiftedHamburger⟩

/-- **A window is the Stieltjes condition on the jets**: `[−a, a]` is nonnegative iff the jet
energies of every even smooth bump on it are the moments of a finite positive measure on
`[0, ∞)`. -/
theorem window_nonneg_iff_stieltjes :
    (∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → 0 ≤ weilQuad G) ↔
      ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → SupportedIn a φ → (∀ x, φ (-x) = φ x) →
        ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
          _root_.HTGeometry.HasStieltjesMoments (jetEnergy φ) ν := by
  constructor
  · intro hW φ hφ hφa hφe
    exact exists_stieltjesMeasure_of_sectors_nonneg (fun G hG hGa _ => hW G hG hGa)
      (fun G hG hGa _ => hW G hG hGa) hφ hφa hφe
  · intro h
    have hne := even_nonneg_of_hamburger fun φ hφ hφa hφe => by
      obtain ⟨ν, hν, hm, -⟩ := h φ hφ hφa hφe
      exact ⟨ν, hν, hm⟩
    have hno : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = -G x) →
        0 ≤ weilQuad G := by
      intro G hG hGa hGo
      obtain ⟨ψ, hψ, hψa, hψe, hψG⟩ := exists_even_antideriv hG hGa hGo
      obtain ⟨ν, -, hm, hsupp⟩ := h ψ hψ hψa hψe
      have h1 := (hm 1).2
      simp only [pow_one, jetEnergy, iteratedDeriv_one, hψG] at h1
      rw [← h1]
      exact integral_nonneg_of_ae hsupp
    exact window_nonneg_of_sectors hne hno

end GaloisForLFunctions.SignedWindowCriticality

end

