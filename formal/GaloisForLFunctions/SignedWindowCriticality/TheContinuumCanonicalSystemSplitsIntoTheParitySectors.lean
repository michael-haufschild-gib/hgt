import GaloisForLFunctions.SignedWindowCriticality.TheJetMinorsArePositiveOnEveryNonnegativeWindow

/-!
# The continuum canonical system splits into the parity sectors

DRAFT
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis DimensionZeroGeometryOfSpecZ
open GrowingWindowsOfSpecZ

variable {φ : ℝ → ℝ}

/-! ### Parity -/

/-- The integral of an even function against an odd one vanishes. -/
theorem integral_even_mul_odd {f g : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (hg : ∀ x, g (-x) = -g x) :
    ∫ u, f u * g u = 0 := by
  have h := integral_neg_eq_self (fun u => f u * g u) volume
  simp only [hf, hg, mul_neg, integral_neg] at h
  linarith

/-- **Odd and even tests are `W`-orthogonal**: Weil's form commutes with the parity. -/
theorem weilPair_odd_even {f g : ℝ → ℝ} (hf : f ∈ realTests) (hg : g ∈ realTests)
    (hfo : ∀ x, f (-x) = -f x) (hge : ∀ x, g (-x) = g x) : weilPair f g = 0 := by
  rw [weilPair_eq_polar hf hg]
  have hR : collarReflect 0 (f - g) = -(f + g) := by
    funext v
    simp only [collarReflect, mul_zero, zero_sub, Pi.sub_apply, Pi.neg_apply, Pi.add_apply, hfo,
      hge]
    ring
  have h1 := weilQuad_collarReflect (f - g) 0
  rw [hR] at h1
  have h2 : weilQuad (-(f + g)) = weilQuad (f + g) := by
    show weilPair (-(f + g)) (-(f + g)) = weilPair (f + g) (f + g)
    rw [weilPair_neg_left, weilPair_neg_right, neg_neg]
  rw [← h1, h2, sub_self, zero_div]

/-- The derivative of an even function is odd. -/
theorem deriv_odd_of_even {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (x : ℝ) :
    deriv f (-x) = -deriv f x := by
  have hfun : f = fun y => f (-y) := funext fun y => (hf y).symm
  have h := deriv_comp_neg (f := f) (x := -x)
  rw [← hfun, neg_neg] at h
  rw [h]

/-- The derivative of an odd function is even. -/
theorem deriv_even_of_odd {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) (x : ℝ) :
    deriv f (-x) = deriv f x := by
  have hfun : f = fun y => -f (-y) := funext fun y => by rw [hf y, neg_neg]
  have h : deriv (fun y => -f (-y)) (-x) = deriv f x := by
    rw [deriv.neg, deriv_comp_neg, neg_neg, neg_neg]
  rw [← hfun] at h
  exact h

/-- The jets of an even bump alternate in parity: `φ^{(k)}(−x) = (−1)^k φ^{(k)}(x)`. -/
theorem iteratedDeriv_parity (hφe : ∀ x, φ (-x) = φ x) (k : ℕ) (x : ℝ) :
    iteratedDeriv k φ (-x) = (-1) ^ k * iteratedDeriv k φ x := by
  induction k generalizing x with
  | zero => simp [hφe]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    rcases Nat.even_or_odd k with hk | hk
    · have he : ∀ y, iteratedDeriv k φ (-y) = iteratedDeriv k φ y := fun y => by
        rw [ih, hk.neg_one_pow, one_mul]
      rw [deriv_odd_of_even he, pow_succ, hk.neg_one_pow]; ring
    · have ho : ∀ y, iteratedDeriv k φ (-y) = -iteratedDeriv k φ y := fun y => by
        rw [ih, hk.neg_one_pow, neg_one_mul]
      rw [deriv_even_of_odd ho, pow_succ, hk.neg_one_pow]; ring

/-! ### Each parity sector is positive definite on smooth tests once nonnegative -/

theorem evenPart_smooth {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun x => (G x + G (-x)) / 2) :=
  (hG.add (hG.comp contDiff_neg)).div_const 2

theorem oddPart_smooth {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun x => (G x - G (-x)) / 2) :=
  (hG.sub (hG.comp contDiff_neg)).div_const 2

theorem supportedIn_evenPart {a : ℝ} {G : ℝ → ℝ} (hG : SupportedIn a G) :
    SupportedIn a (fun x => (G x + G (-x)) / 2) := fun u hu => by
  simp [hG u hu, hG (-u) (by rwa [abs_neg])]

theorem supportedIn_oddPart {a : ℝ} {G : ℝ → ℝ} (hG : SupportedIn a G) :
    SupportedIn a (fun x => (G x - G (-x)) / 2) := fun u hu => by
  simp [hG u hu, hG (-u) (by rwa [abs_neg])]

/-- A sector minimizer is a window eigenfunction: the sector variation plus parity orthogonality
give the eigen-equation against every test. -/
theorem isWindowEigen_of_sector_isMin {a : ℝ} {H : ℝ → ℝ} (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hH : ContDiff ℝ ∞ H) (hHa : SupportedIn a H) (hHp : ∀ x, H (-x) = ε * H x)
    (hnn : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = ε * G x) →
      0 ≤ weilQuad G)
    (h0 : weilQuad H = 0) : IsWindowEigen a 0 H := by
  have hHr := smooth_mem_realTests hH hHa
  -- the variation inside the sector
  have hsec : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = ε * G x) →
      weilPair H G = 0 := by
    intro G hG hGa hGp
    have hGr := smooth_mem_realTests hG hGa
    refine eq_zero_of_forall_quadratic_nonneg (Y := weilQuad G) fun t => ?_
    have hf := hnn (H + t • G) (smooth_add_smul hH hG t) (supportedIn_add_smul hHa hGa t)
      (fun x => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hHp, hGp]; ring)
    rw [weilQuad_add hHr (realTests.smul_mem t hGr), h0, weilPair_smul_right] at hf
    have e2 : weilQuad (t • G) = t ^ 2 * weilQuad G := by
      show weilPair (t • G) (t • G) = _
      rw [weilPair_smul_left, weilPair_smul_right, show weilQuad G = weilPair G G from rfl]; ring
    rw [e2] at hf
    linarith
  intro G hG hGa
  rw [zero_mul]
  set Ge := fun x => (G x + G (-x)) / 2
  set Go := fun x => (G x - G (-x)) / 2
  have hGeq : G = Ge + Go := by funext x; simp only [Ge, Go, Pi.add_apply]; ring
  have hGer := smooth_mem_realTests (evenPart_smooth hG) (supportedIn_evenPart hGa)
  have hGor := smooth_mem_realTests (oddPart_smooth hG) (supportedIn_oddPart hGa)
  rw [hGeq, weilPair_add_right hHr hGer hGor]
  have hGe : ∀ x, Ge (-x) = Ge x := fun x => by simp only [Ge, neg_neg]; ring
  have hGo : ∀ x, Go (-x) = -Go x := fun x => by simp only [Go, neg_neg]; ring
  rcases hε with rfl | rfl
  · rw [hsec Ge (evenPart_smooth hG) (supportedIn_evenPart hGa) (fun x => by rw [hGe, one_mul]),
      weilPair_comm, weilPair_odd_even hGor hHr hGo (fun x => by rw [hHp, one_mul]), add_zero]
  · rw [hsec Go (oddPart_smooth hG) (supportedIn_oddPart hGa) (fun x => by rw [hGo, neg_one_mul]),
      weilPair_odd_even hHr hGer (fun x => by rw [hHp, neg_one_mul]) hGe, zero_add]

/-- **Each parity sector is positive definite on smooth tests once nonnegative**: if Weil's form
is nonnegative on the smooth tests of `[−a, a]` of parity `ε`, it is positive on every nonzero one.
A sector zero mode — in particular the zero mode of a first failure of one sector — is never
smooth. -/
theorem weilQuad_pos_of_sector_nonneg {a : ℝ} (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hnn : ∀ G : ℝ → ℝ, ContDiff ℝ ∞ G → SupportedIn a G → (∀ x, G (-x) = ε * G x) →
      0 ≤ weilQuad G)
    {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H) (hHa : SupportedIn a H) (hHp : ∀ x, H (-x) = ε * H x)
    (hne : H ≠ 0) : 0 < weilQuad H :=
  lt_of_le_of_ne (hnn H hH hHa hHp) fun h0 =>
    hne (eq_zero_of_isWindowEigen hH hHa (isWindowEigen_of_sector_isMin ε hε hH hHa hHp hnn h0.symm))

/-! ### The jet Gram splits by parity -/

/-- The even-order jet Gram `[W(φ^{(2p)}, φ^{(2q)})]_{p,q<m}`. -/
def evenJetGram (φ : ℝ → ℝ) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun p q => weilPair (iteratedDeriv (2 * p) φ) (iteratedDeriv (2 * q) φ)

/-- The odd-order jet Gram `[W(φ^{(2p+1)}, φ^{(2q+1)})]_{p,q<m}`. -/
def oddJetGram (φ : ℝ → ℝ) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun p q => weilPair (iteratedDeriv (2 * p + 1) φ) (iteratedDeriv (2 * q + 1) φ)

/-- The parity split `Fin ⌈n/2⌉ ⊕ Fin ⌊n/2⌋ ≃ Fin n`, `p ↦ 2p`, `q ↦ 2q + 1`. -/
def paritySplit (n : ℕ) : Fin ((n + 1) / 2) ⊕ Fin (n / 2) ≃ Fin n where
  toFun s := match s with
    | Sum.inl p => ⟨2 * p, by omega⟩
    | Sum.inr q => ⟨2 * q + 1, by omega⟩
  invFun i := if (i : ℕ) % 2 = 0 then Sum.inl ⟨i / 2, by omega⟩ else Sum.inr ⟨i / 2, by omega⟩
  left_inv s := by
    rcases s with p | q
    · simp only
      rw [if_pos (by omega)]
      congr 1; ext; simp only; omega
    · simp only
      rw [if_neg (by omega)]
      congr 1; ext; simp only; omega
  right_inv i := by
    by_cases h : (i : ℕ) % 2 = 0
    · simp only [h, if_true]; ext; simp only; omega
    · simp only [h, if_false]; ext; simp only; omega

/-- **The jet Gram is block diagonal in the parities**: `det J_n = det E_{⌈n/2⌉} · det O_{⌊n/2⌋}`. -/
theorem det_jetGram_eq_mul (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (n : ℕ) :
    (jetGram φ n).det = (evenJetGram φ ((n + 1) / 2)).det * (oddJetGram φ (n / 2)).det := by
  have hblock : (jetGram φ n).submatrix (paritySplit n) (paritySplit n) =
      Matrix.fromBlocks (evenJetGram φ ((n + 1) / 2)) 0 0 (oddJetGram φ (n / 2)) := by
    ext s t
    rcases s with p | q <;> rcases t with p' | q'
    · simp [paritySplit, jetGram, evenJetGram]
    · simp only [paritySplit, jetGram, Matrix.submatrix_apply, Equiv.coe_fn_mk, Matrix.of_apply,
        Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      exact weilPair_iteratedDeriv_eq_zero_of_odd hφ hφc ⟨p + q', by ring⟩
    · simp only [paritySplit, jetGram, Matrix.submatrix_apply, Equiv.coe_fn_mk, Matrix.of_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      exact weilPair_iteratedDeriv_eq_zero_of_odd hφ hφc ⟨q + p', by ring⟩
    · simp [paritySplit, jetGram, oddJetGram]
  rw [← Matrix.det_submatrix_equiv_self (paritySplit n), hblock, Matrix.det_fromBlocks_zero₂₁]

/-- **The continuum margins read the parity sectors**: with all jet minors nonzero, the even-order
margins are the even-jet Stieltjes ratios and the odd-order margins the odd-jet ones:
`h^{−4m}E_{2m} → det E_{m+1}/det E_m` and `h^{−4m−2}E_{2m+1} → det O_{m+1}/det O_m`. -/
theorem tendsto_levinsonErr_even_odd (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (m : ℕ)
    (hE : ∀ k ≤ m + 1, (evenJetGram φ k).det ≠ 0) (hO : ∀ k ≤ m + 1, (oddJetGram φ k).det ≠ 0) :
    Tendsto (fun h => levinsonErr (weilSeq φ h) (2 * m) / h ^ (2 * (2 * m))) (𝓝[>] 0)
        (𝓝 ((evenJetGram φ (m + 1)).det / (evenJetGram φ m).det)) ∧
      Tendsto (fun h => levinsonErr (weilSeq φ h) (2 * m + 1) / h ^ (2 * (2 * m + 1))) (𝓝[>] 0)
        (𝓝 ((oddJetGram φ (m + 1)).det / (oddJetGram φ m).det)) := by
  have hJ : ∀ n ≤ 2 * m + 2, (jetGram φ n).det ≠ 0 := fun n hn => by
    rw [det_jetGram_eq_mul hφ hφc]
    exact mul_ne_zero (hE _ (by omega)) (hO _ (by omega))
  constructor
  · have h := tendsto_levinsonErr_div_pow hφ hφc (2 * m) fun k hk => hJ (k + 1) (by omega)
    have e1 : (jetGram φ (2 * m + 1)).det / (jetGram φ (2 * m)).det =
        (evenJetGram φ (m + 1)).det / (evenJetGram φ m).det := by
      rw [det_jetGram_eq_mul hφ hφc, det_jetGram_eq_mul hφ hφc,
        show (2 * m + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1) / 2 = m by omega,
        show (2 * m + 1) / 2 = m by omega, show 2 * m / 2 = m by omega]
      have := hO m (by omega)
      field_simp
    rwa [e1] at h
  · have h := tendsto_levinsonErr_div_pow hφ hφc (2 * m + 1) fun k hk => hJ (k + 1) (by omega)
    have e1 : (jetGram φ (2 * m + 1 + 1)).det / (jetGram φ (2 * m + 1)).det =
        (oddJetGram φ (m + 1)).det / (oddJetGram φ m).det := by
      rw [det_jetGram_eq_mul hφ hφc, det_jetGram_eq_mul hφ hφc,
        show (2 * m + 1 + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
        show (2 * m + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1) / 2 = m by omega]
      have := hE (m + 1) (by omega)
      field_simp
    rwa [e1] at h

end GaloisForLFunctions.SignedWindowCriticality

end
