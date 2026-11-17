import GaloisForLFunctions.OrderSixMetaplecticTheory.TheLongColumnsAreLayersOfTwistedThetaSquares

/-!
# The Weil index is a Klein combination

On the odd classes modulo `4` write `c³ ≡ 1 + 2(t₁ + t₂ω)` (cubing kills `μ₃`; `(1 + 2O)/(1 + 4O) ≅ 𝔽₄`). The
Klein characters are `κ₁ = (−1)^{t₂}`, `κ_{ω²} = (−1)^{t₁}`, `κ_ω = κ₁κ_{ω²}` (`κ_s(1 + 2t) = (−1)^{tr(st)}`), and

`Γ(c) = ½(1 + κ₁(c)) + (i/2)(κ_{ω²}(c) − κ_ω(c))`   (`fixedDualAverage_eq_klein`):

`Γ` takes the values `1, 1, i, −i` at `1, −1, 1 + 2ω, 1 + 2ω²`. The bicharacter `r(n, ·)` is multiplicative on
odd classes (`phaseTwist`), so every long column is four `ω²λ²`-layers with explicit coefficients
(`columnSeries_eq_klein`):

`Σ_A g_{gen A}(n)/|gen A| N(A)^{−w} = ½\overline{S^{Ξ₀}} + ½\overline{S^{Ξ₁}} + (i/2)\overline{S^{Ξ_{ω²}}} − (i/2)\overline{S^{Ξ_ω}}`,

`Ξ_s = \overline{r(n, ·)κ_sχ₂(·/n)₃(·/n)₂}`. At column `1` this is the order-six family itself
(`orderSixSeries_eq_klein`): one cubic layer `χ₂` (weight `½`) and three Klein layers, two of them odd
(`κ_ω(−1) = κ_{ω²}(−1) = −1`).
-/

noncomputable section

open MeasureTheory UniqueFactorizationMonoid
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.Eisenstein.Coordinates MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicJacobi SpectralTheoryOfTheCubicCover

/-! ### Klein characters in coordinates -/

/-- First coordinate of `c³` modulo `4`. -/
def cubeFst (a b : ZMod 4) : ZMod 4 := mulFst (mulFst a b a b) (mulSnd a b a b) a b

/-- Second coordinate of `c³` modulo `4`. -/
def cubeSnd (a b : ZMod 4) : ZMod 4 := mulSnd (mulFst a b a b) (mulSnd a b a b) a b

/-- `κ₁ = (−1)^{t₂}`. -/
def kleinOneZ (a b : ZMod 4) : ℤ := if cubeSnd a b = 2 then -1 else 1

/-- `κ_{ω²} = (−1)^{t₁}`. -/
def kleinOmegaSqZ (a b : ZMod 4) : ℤ := if cubeFst a b = 3 then -1 else 1

/-- `κ_ω = κ₁ κ_{ω²}`. -/
def kleinOmegaZ (a b : ZMod 4) : ℤ := kleinOneZ a b * kleinOmegaSqZ a b

/-- The indicator of the odd classes. -/
def oddZ (_ _ : ZMod 4) : ℤ := 1

theorem kleinOneZ_mul : ∀ a b c d : ZMod 4, oddCoord a b → oddCoord c d →
    kleinOneZ (mulFst a b c d) (mulSnd a b c d) = kleinOneZ a b * kleinOneZ c d := by decide

theorem kleinOmegaSqZ_mul : ∀ a b c d : ZMod 4, oddCoord a b → oddCoord c d →
    kleinOmegaSqZ (mulFst a b c d) (mulSnd a b c d) = kleinOmegaSqZ a b * kleinOmegaSqZ c d := by decide

theorem kleinOmegaZ_mul (a b c d : ZMod 4) (h₁ : oddCoord a b) (h₂ : oddCoord c d) :
    kleinOmegaZ (mulFst a b c d) (mulSnd a b c d) = kleinOmegaZ a b * kleinOmegaZ c d := by
  unfold kleinOmegaZ
  rw [kleinOneZ_mul a b c d h₁ h₂, kleinOmegaSqZ_mul a b c d h₁ h₂]
  ring

/-- **`2Γ = 1 + κ₁ + i(κ_{ω²} − κ_ω)` on the odd classes.** -/
theorem twoGamma_klein : ∀ a b : ZMod 4, oddCoord a b →
    twoGamma a b = 1 + (kleinOneZ a b : GaussianInt) +
      ⟨0, 1⟩ * ((kleinOmegaSqZ a b : GaussianInt) - (kleinOmegaZ a b : GaussianInt)) := by decide

theorem not_mem_two_one : (1 : O) ∉ Ideal.span {(2 : O)} := by
  rw [Ideal.mem_span_singleton]
  exact two_prime.not_dvd_one

theorem coords_one : coords (1 : O) = (1, 0) := by
  rw [show (1 : O) = eval 1 0 by simp [eval], coords_eval]

/-- A function of the coordinates modulo `4`, multiplicative on odd classes, as a character on `O` (zero on even
elements). -/
def kleinChar (k : ZMod 4 → ZMod 4 → ℤ) (h1 : k 1 0 = 1)
    (hk : ∀ a b c d : ZMod 4, oddCoord a b → oddCoord c d → k (mulFst a b c d) (mulSnd a b c d) = k a b * k c d) :
    O →* ℂ where
  toFun x := if x ∈ Ideal.span {(2 : O)} then 0 else (k ((coords x).1 : ZMod 4) ((coords x).2 : ZMod 4) : ℂ)
  map_one' := by
    rw [if_neg not_mem_two_one, coords_one]
    simp [h1]
  map_mul' x y := by
    by_cases hx : x ∈ Ideal.span {(2 : O)}
    · rw [if_pos (Ideal.mul_mem_right y _ hx), if_pos hx, zero_mul]
    by_cases hy : y ∈ Ideal.span {(2 : O)}
    · rw [if_pos (Ideal.mul_mem_left _ x hy), if_pos hy, mul_zero]
    rw [if_neg (odd_mul hx hy), if_neg hx, if_neg hy]
    obtain ⟨a, b, rfl⟩ := exists_eval x
    obtain ⟨c, d, rfl⟩ := exists_eval y
    rw [eval_mul, coords_eval, coords_eval, coords_eval]
    simp only
    rw [← mulFst_cast, ← mulSnd_cast,
      hk _ _ _ _ (oddCoord_of_not_mem _ _ hx) (oddCoord_of_not_mem _ _ hy)]
    push_cast
    ring

theorem kleinChar_eval (k : ZMod 4 → ZMod 4 → ℤ) (h1 : k 1 0 = 1)
    (hk : ∀ a b c d : ZMod 4, oddCoord a b → oddCoord c d → k (mulFst a b c d) (mulSnd a b c d) = k a b * k c d)
    (a b : ℤ) (h2 : eval a b ∉ Ideal.span {(2 : O)}) :
    kleinChar k h1 hk (eval a b) = (k (a : ZMod 4) (b : ZMod 4) : ℂ) := by
  change (if eval a b ∈ Ideal.span {(2 : O)} then 0 else _) = _
  rw [if_neg h2, coords_eval]

theorem kleinChar_even (k : ZMod 4 → ZMod 4 → ℤ) (h1 : k 1 0 = 1)
    (hk : ∀ a b c d : ZMod 4, oddCoord a b → oddCoord c d → k (mulFst a b c d) (mulSnd a b c d) = k a b * k c d)
    (c : O) (h2 : (2 : O) ∣ c) : kleinChar k h1 hk c = 0 := by
  change (if c ∈ Ideal.span {(2 : O)} then 0 else _) = _
  rw [if_pos (Ideal.mem_span_singleton.mpr h2)]

theorem kleinChar_norm_le (k : ZMod 4 → ZMod 4 → ℤ) (h1 : k 1 0 = 1)
    (hk : ∀ a b c d : ZMod 4, oddCoord a b → oddCoord c d → k (mulFst a b c d) (mulSnd a b c d) = k a b * k c d)
    (hb : ∀ a b, k a b = 1 ∨ k a b = -1) (c : O) : ‖kleinChar k h1 hk c‖ ≤ 1 := by
  change ‖(if c ∈ Ideal.span {(2 : O)} then 0 else (k ((coords c).1 : ZMod 4) ((coords c).2 : ZMod 4) : ℂ))‖ ≤ 1
  split_ifs
  · simp
  · rcases hb ((coords c).1 : ZMod 4) ((coords c).2 : ZMod 4) with h | h <;> simp [h]

/-- The odd indicator `κ₀`. -/
def kleinZero : O →* ℂ := kleinChar oddZ rfl (fun _ _ _ _ _ _ => by simp [oddZ])

/-- `κ₁`. -/
def kleinOne : O →* ℂ := kleinChar kleinOneZ (by decide) kleinOneZ_mul

/-- `κ_{ω²}`. -/
def kleinOmegaSq : O →* ℂ := kleinChar kleinOmegaSqZ (by decide) kleinOmegaSqZ_mul

/-- `κ_ω`. -/
def kleinOmega : O →* ℂ := kleinChar kleinOmegaZ (by decide) kleinOmegaZ_mul

theorem kleinOneZ_sign : ∀ a b : ZMod 4, kleinOneZ a b = 1 ∨ kleinOneZ a b = -1 := by decide
theorem kleinOmegaSqZ_sign : ∀ a b : ZMod 4, kleinOmegaSqZ a b = 1 ∨ kleinOmegaSqZ a b = -1 := by decide
theorem kleinOmegaZ_sign : ∀ a b : ZMod 4, kleinOmegaZ a b = 1 ∨ kleinOmegaZ a b = -1 := by decide

/-- **`Γ(c) = ½(1 + κ₁(c)) + (i/2)(κ_{ω²}(c) − κ_ω(c))` on the odd classes.** -/
theorem fixedDualAverage_eq_klein (c : O) (hc : c ∉ Ideal.span {(2 : O)}) :
    fixedDualAverage c = (1 / 2 : ℂ) * kleinZero c + (1 / 2 : ℂ) * kleinOne c +
      (Complex.I / 2) * kleinOmegaSq c - (Complex.I / 2) * kleinOmega c := by
  obtain ⟨a, b, rfl⟩ := exists_eval c
  have h := congrArg GaussianInt.toComplex (twoGamma_klein (a : ZMod 4) (b : ZMod 4) (oddCoord_of_not_mem _ _ hc))
  simp only [map_add, map_mul, map_sub, map_one, map_intCast] at h
  have hI : GaussianInt.toComplex ⟨0, 1⟩ = Complex.I := by
    simp [GaussianInt.toComplex_def]
  rw [hI] at h
  have h0 : kleinZero (eval a b) = 1 := by
    rw [kleinZero, kleinChar_eval _ _ _ _ _ hc, show oddZ (a : ZMod 4) (b : ZMod 4) = 1 from rfl, Int.cast_one]
  rw [fixedDualAverage_eval, h, h0, kleinOne, kleinOmegaSq, kleinOmega, kleinChar_eval _ _ _ _ _ hc,
    kleinChar_eval _ _ _ _ _ hc, kleinChar_eval _ _ _ _ _ hc]
  ring

/-! ### The quadratic phase and the cubic character at two -/

theorem fixedDualAverage_one : fixedDualAverage (1 : O) = 1 := by
  have h := fixedDualAverage_eval 1 0
  rw [show eval 1 0 = 1 by simp [eval]] at h
  rw [h]
  have h2 : twoGamma ((1 : ℤ) : ZMod 4) ((0 : ℤ) : ZMod 4) = 2 := by decide
  rw [h2, map_ofNat]
  norm_num

theorem quadraticPhase_one_right (n : O) (hn : n ∉ Ideal.span {(2 : O)}) : quadraticPhase n 1 = 1 := by
  rw [quadraticPhase, mul_one, fixedDualAverage_one, mul_one, div_self (gamma_ne_zero hn)]

/-- `c ↦ \overline{r(n, c)}` on odd classes, `0` on even ones. -/
def phaseTwist (n : O) (hn : n ∉ Ideal.span {(2 : O)}) : O →* ℂ where
  toFun c := if c ∈ Ideal.span {(2 : O)} then 0 else star (quadraticPhase n c)
  map_one' := by rw [if_neg not_mem_two_one, quadraticPhase_one_right n hn, star_one]
  map_mul' x y := by
    by_cases hx : x ∈ Ideal.span {(2 : O)}
    · rw [if_pos (Ideal.mul_mem_right y _ hx), if_pos hx, zero_mul]
    by_cases hy : y ∈ Ideal.span {(2 : O)}
    · rw [if_pos (Ideal.mul_mem_left _ x hy), if_pos hy, mul_zero]
    rw [if_neg (odd_mul hx hy), if_neg hx, if_neg hy, quadraticPhase_comm,
      quadraticPhase_mul_left hx hy hn, quadraticPhase_comm x, quadraticPhase_comm y, star_mul']

theorem phaseTwist_norm_le (n : O) (hn : n ∉ Ideal.span {(2 : O)}) (c : O) : ‖phaseTwist n hn c‖ ≤ 1 := by
  change ‖(if c ∈ Ideal.span {(2 : O)} then 0 else star (quadraticPhase n c))‖ ≤ 1
  split_ifs with hc
  · simp
  · have hs := quadraticPhase_sq hn hc
    have hn1 : ‖quadraticPhase n c‖ ^ 2 = 1 := by rw [← norm_pow, hs, norm_one]
    rw [norm_star]
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp hn1)

/-- `χ₂` as a character on `O`. -/
def cubicTwoHom : O →* ℂ where
  toFun := cubicTwoChar
  map_one' := by
    unfold cubicTwoChar
    rw [symbol_one_numerator (-2) primary_neg_two, map_one, one_pow]
  map_mul' := cubicTwoChar_mul

theorem cubicTwoHom_norm_le (c : O) : ‖cubicTwoHom c‖ ≤ 1 := by
  change ‖ringComplex (symbol c (-2)) ^ 2‖ ≤ 1
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_symbol_le c (-2) primary_neg_two)

/-! ### The long columns as four layers -/

/-- The 2-adic factors `r̄(n, ·)κ_sχ₂` for `s = 0, 1, ω², ω`. -/
def kleinFactor (n : O) (hn : n ∉ Ideal.span {(2 : O)}) : Fin 4 → O →* ℂ :=
  ![phaseTwist n hn * kleinZero * cubicTwoHom, phaseTwist n hn * kleinOne * cubicTwoHom,
    phaseTwist n hn * kleinOmegaSq * cubicTwoHom, phaseTwist n hn * kleinOmega * cubicTwoHom]

/-- The Klein coefficients of `Γ`: `½, ½, i/2, −i/2`. -/
def kleinCoeff : Fin 4 → ℂ := ![1 / 2, 1 / 2, Complex.I / 2, -(Complex.I / 2)]

theorem kleinCoeff_zero : kleinCoeff 0 = 1 / 2 := rfl
theorem kleinCoeff_one : kleinCoeff 1 = 1 / 2 := rfl
theorem kleinCoeff_two : kleinCoeff 2 = Complex.I / 2 := rfl
theorem kleinCoeff_three : kleinCoeff 3 = -(Complex.I / 2) := rfl

theorem kleinFactor_zero (n : O) (hn : n ∉ Ideal.span {(2 : O)}) :
    kleinFactor n hn 0 = phaseTwist n hn * kleinZero * cubicTwoHom := rfl
theorem kleinFactor_one (n : O) (hn : n ∉ Ideal.span {(2 : O)}) :
    kleinFactor n hn 1 = phaseTwist n hn * kleinOne * cubicTwoHom := rfl
theorem kleinFactor_two (n : O) (hn : n ∉ Ideal.span {(2 : O)}) :
    kleinFactor n hn 2 = phaseTwist n hn * kleinOmegaSq * cubicTwoHom := rfl
theorem kleinFactor_three (n : O) (hn : n ∉ Ideal.span {(2 : O)}) :
    kleinFactor n hn 3 = phaseTwist n hn * kleinOmega * cubicTwoHom := rfl

theorem not_mem_two_of_not_dvd {c : O} (h : ¬ (2 : O) ∣ c) : c ∉ Ideal.span {(2 : O)} := by
  rwa [Ideal.mem_span_singleton]

theorem twoAdicWeight_klein (n : O) (hn : n ∉ Ideal.span {(2 : O)}) (c : O) (hc : ¬ (2 : O) ∣ c) :
    twoAdicWeight n c = ∑ i : Fin 4, kleinCoeff i * kleinFactor n hn i c := by
  have hc' := not_mem_two_of_not_dvd hc
  have hp : phaseTwist n hn c = star (quadraticPhase n c) := by
    change (if c ∈ Ideal.span {(2 : O)} then 0 else star (quadraticPhase n c)) = _
    rw [if_neg hc']
  rw [Fin.sum_univ_four, kleinCoeff_zero, kleinCoeff_one, kleinCoeff_two, kleinCoeff_three, kleinFactor_zero,
    kleinFactor_one, kleinFactor_two, kleinFactor_three]
  simp only [MonoidHom.mul_apply, hp]
  unfold twoAdicWeight
  rw [fixedDualAverage_eq_klein c hc']
  change _ = _ * (_ * _ * cubicTwoChar c) + _ * (_ * _ * cubicTwoChar c) + _ * (_ * _ * cubicTwoChar c) +
    _ * (_ * _ * cubicTwoChar c)
  ring

theorem kleinFactor_norm_le (n : O) (hn : n ∉ Ideal.span {(2 : O)}) (i : Fin 4) (c : O) :
    ‖kleinFactor n hn i c‖ ≤ 1 := by
  have hk : ∀ κ : O →* ℂ, (∀ c, ‖κ c‖ ≤ 1) → ‖(phaseTwist n hn * κ * cubicTwoHom) c‖ ≤ 1 := by
    intro κ hκ
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, norm_mul, norm_mul]
    exact mul_le_one₀ (mul_le_one₀ (phaseTwist_norm_le n hn c) (norm_nonneg _) (hκ c)) (norm_nonneg _)
      (cubicTwoHom_norm_le c)
  fin_cases i
  · exact hk _ (kleinChar_norm_le _ _ _ (fun _ _ => Or.inl rfl))
  · exact hk _ (kleinChar_norm_le _ _ _ kleinOneZ_sign)
  · exact hk _ (kleinChar_norm_le _ _ _ kleinOmegaSqZ_sign)
  · exact hk _ (kleinChar_norm_le _ _ _ kleinOmegaZ_sign)

theorem kleinFactor_even (n : O) (hn : n ∉ Ideal.span {(2 : O)}) (i : Fin 4) (c : O) (h2 : (2 : O) ∣ c) :
    kleinFactor n hn i c = 0 := by
  have hp : phaseTwist n hn c = 0 := by
    change (if c ∈ Ideal.span {(2 : O)} then 0 else star (quadraticPhase n c)) = 0
    rw [if_pos (Ideal.mem_span_singleton.mpr h2)]
  fin_cases i <;> simp [kleinFactor, MonoidHom.mul_apply, hp]

theorem not_mem_two_of_isCoprime {n : O} (hn2 : IsCoprime n 2) : n ∉ Ideal.span {(2 : O)} := by
  rw [Ideal.mem_span_singleton]
  intro hd
  exact two_prime.not_unit (hn2.isUnit_of_dvd' hd (dvd_refl 2))

/-- **Every long column is four `ω²λ²`-layers with the Klein coefficients of the Weil index:**
`Σ_A g_{gen A}(n)/|gen A| N(A)^{−w} = Σ_s γ_s \overline{S^{Ξ_s}_{ω²λ²}(w̄)}`, `γ = (½, ½, i/2, −i/2)`,
`Ξ_s = \overline{r(n, ·)κ_sχ₂(·/n)₃(·/n)₂}`. -/
theorem columnSeries_eq_klein (n : O) (hn : lambda ^ 2 ∣ n - 1) (hn0 : n ≠ 0) (hn2 : IsCoprime n 2) (w : ℂ)
    (hw : 1 < w.re) :
    columnSeries n w = ∑ i : Fin 4, kleinCoeff i *
      star (twistedSquarefreeSeriesG (layerTwist (kleinFactor n (not_mem_two_of_isCoprime hn2) i) n hn hn0 hn2)
        (omega ^ 2 * lambda ^ 2) (star w)) :=
  columnSeries_eq_of_expansion Finset.univ kleinCoeff (kleinFactor n _) n hn hn0 hn2
    (kleinFactor_norm_le n _) (kleinFactor_even n _) (twoAdicWeight_klein n _) w hw

/-! ### Column one: the order-six family -/

/-- The first moment series of the order-six family `Σ_A ω₆(gen A) N(A)^{−w}` over squarefree odd rows. -/
def orderSixSeries (w : ℂ) : ℂ := ∑' A : Ideal O, orderSixCoefficient A * unramifiedNormWeight w A

theorem columnCoefficient_one (A : Ideal O) : columnCoefficient 1 A = orderSixCoefficient A := by
  unfold columnCoefficient orderSixCoefficient
  split_ifs with h
  · have hc := not_mem_two_of_not_dvd h.2.2
    unfold columnWeight
    rw [symbol_one, quadSymbol_one_denominator, quadraticPhase, one_mul, fixedDualAverage_one, one_mul,
      div_self (gamma_ne_zero hc), star_one, map_one, one_mul, one_mul, one_mul]
  · rfl

theorem orderSixSeries_eq_column (w : ℂ) : orderSixSeries w = columnSeries 1 w := by
  unfold orderSixSeries columnSeries
  simp only [columnCoefficient_one]

/-- **The order-six family is one cubic layer and three Klein layers.** For `Re w > 1`,
`Σ_A ω₆(gen A)N(A)^{−w} = ½\overline{S^{Ξ₀}} + ½\overline{S^{Ξ₁}} + (i/2)\overline{S^{Ξ_{ω²}}} − (i/2)\overline{S^{Ξ_ω}}`
(layers at `ω²λ²`, argument `w̄`), `Ξ_s = \overline{κ_sχ₂}` on odd classes. -/
theorem orderSixSeries_eq_klein (w : ℂ) (hw : 1 < w.re) :
    orderSixSeries w = ∑ i : Fin 4, kleinCoeff i *
      star (twistedSquarefreeSeriesG
        (layerTwist (kleinFactor 1 (not_mem_two_of_isCoprime isCoprime_one_left) i) 1 (by simp) one_ne_zero
          isCoprime_one_left) (omega ^ 2 * lambda ^ 2) (star w)) := by
  rw [orderSixSeries_eq_column]
  exact columnSeries_eq_klein 1 (by simp) one_ne_zero isCoprime_one_left w hw

end GaloisForLFunctions.OrderSixMetaplecticTheory
