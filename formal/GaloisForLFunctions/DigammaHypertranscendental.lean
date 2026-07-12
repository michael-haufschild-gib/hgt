import GaloisForLFunctions.HolderShiftElimination
import GaloisForLFunctions.GammaDifferentialFE
import GaloisForLFunctions.Hypertranscendence

/-!
# Hölder's theorem for the digamma function

`ψ = Γ'/Γ` satisfies no algebraic differential equation over `ℂ[s]`:
`Hypertranscendental Complex.digamma`.

The proof feeds the shift-elimination engine.  A hypothetical annihilating differential
polynomial is reshaped so the point variable becomes the polynomial coefficient
(`reshapeJet`), producing a polynomial-coefficient jet relation that vanishes off the poles
(`AnnihilatesDigamma`).  The set of rational-coefficient jet polynomials admitting a
denominator-cleared annihilating form (`digammaAnnihilator`) is closed under subtraction and
`ℂ(X)`-scalars by ring-homomorphism algebra, contains no nonzero constant because a nonzero
polynomial has finitely many roots, and is stable under the jet substitution because the
differentiated shift law `ψ⁽ʲ⁾(z+1) = ψ⁽ʲ⁾(z) + (−1)ʲ·j!/z^{j+1}` converts the cleared
substitution `Y_j ↦ X^m·Y_j + (−1)ʲ·j!·X^{m−1−j}` (`clearedShift`) into evaluation at
`z + 1`.  The engine `no_shift_stable_annihilator` then yields the contradiction.
-/

noncomputable section

namespace GaloisForLFunctions

open MvPolynomial

/-! ## The differentiated shift law -/

/-- The digamma jet vector: `digammaJet m z j = ψ⁽ʲ⁾(z)`. -/
def digammaJet (m : ℕ) (z : ℂ) : Fin m → ℂ :=
  fun j => iteratedDeriv (j : ℕ) Complex.digamma z

/-- **The differentiated shift law of digamma:**
`ψ⁽ʲ⁾(z+1) = ψ⁽ʲ⁾(z) + (−1)ʲ·j!/z^{j+1}` off the poles. -/
theorem digammaJet_shift (j : ℕ) {z : ℂ} (hz : ∀ p : ℕ, z ≠ -(p : ℂ)) :
    iteratedDeriv j Complex.digamma (z + 1)
      = iteratedDeriv j Complex.digamma z
        + (-1) ^ j * (j.factorial : ℂ) / z ^ (j + 1) := by
  have hψ : (fun w => deriv Complex.Gamma w / Complex.Gamma w) = Complex.digamma := by
    funext w
    rw [Complex.digamma_def, logDeriv_apply]
  have h := polygamma_recurrence j z hz
  rw [hψ] at h
  linear_combination h

/-! ## Polynomial-coefficient jet evaluation -/

/-- Evaluation of a polynomial-coefficient jet polynomial: coefficients evaluate at `z`,
the `j`-th jet variable evaluates to `ψ⁽ʲ⁾(z)`. -/
def polyJetEval (m : ℕ) (z : ℂ) :
    MvPolynomial (Fin m) (Polynomial ℂ) →+* ℂ :=
  eval₂Hom (Polynomial.evalRingHom z) (digammaJet m z)

/-- A polynomial-coefficient jet polynomial annihilates the digamma jets off the poles. -/
def AnnihilatesDigamma (m : ℕ) (G : MvPolynomial (Fin m) (Polynomial ℂ)) : Prop :=
  ∀ z : ℂ, (∀ p : ℕ, z ≠ -(p : ℂ)) → polyJetEval m z G = 0

theorem polyJetEval_C (m : ℕ) (z : ℂ) (p : Polynomial ℂ) :
    polyJetEval m z (C p) = p.eval z := by
  simp [polyJetEval]

/-! ## Reshaping a differential polynomial -/

/-- Reshape a differential polynomial: the point variable becomes the polynomial
coefficient, the jet variables shift down by one. -/
def reshapeJet (n : ℕ) :
    MvPolynomial (Fin (n + 2)) ℂ →+* MvPolynomial (Fin (n + 1)) (Polynomial ℂ) :=
  eval₂Hom ((MvPolynomial.C).comp (Polynomial.C))
    (Fin.cases (MvPolynomial.C Polynomial.X) (fun j => MvPolynomial.X j))

/-- The inverse reshaping: the polynomial coefficient re-expands into the point variable. -/
def reshapeJetInv (n : ℕ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) →+* MvPolynomial (Fin (n + 2)) ℂ :=
  eval₂Hom (Polynomial.eval₂RingHom (MvPolynomial.C) (MvPolynomial.X 0))
    (fun j => MvPolynomial.X j.succ)

theorem reshapeJetInv_comp_reshapeJet (n : ℕ) :
    (reshapeJetInv n).comp (reshapeJet n) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [reshapeJet, reshapeJetInv]
  · intro i
    induction i using Fin.cases with
    | zero => simp [reshapeJet, reshapeJetInv]
    | succ j => simp [reshapeJet, reshapeJetInv]

theorem reshapeJet_injective (n : ℕ) : Function.Injective (reshapeJet n) := by
  intro a b h
  have ha := RingHom.congr_fun (reshapeJetInv_comp_reshapeJet n) a
  have hb := RingHom.congr_fun (reshapeJetInv_comp_reshapeJet n) b
  rw [RingHom.comp_apply] at ha hb
  rw [RingHom.id_apply] at ha hb
  rw [← ha, ← hb, h]

/-- Reshaped evaluation is jet evaluation with the point in slot zero. -/
theorem polyJetEval_reshapeJet (n : ℕ) (z : ℂ) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    polyJetEval (n + 1) z (reshapeJet n P)
      = MvPolynomial.eval
          (Fin.cons z fun j : Fin (n + 1) =>
            iteratedDeriv (j : ℕ) Complex.digamma z) P := by
  have hhom : ((polyJetEval (n + 1) z).comp (reshapeJet n))
      = (MvPolynomial.eval (Fin.cons z fun j : Fin (n + 1) =>
          iteratedDeriv (j : ℕ) Complex.digamma z) : _ →+* ℂ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [polyJetEval, reshapeJet]
    · intro i
      induction i using Fin.cases with
      | zero =>
          simp [polyJetEval, reshapeJet]
      | succ j =>
          simp [polyJetEval, reshapeJet, digammaJet, Fin.cons_succ]
  exact RingHom.congr_fun hhom P

/-! ## The denominator-cleared annihilator set -/

/-- Rational-coefficient jet polynomials with a denominator-cleared polynomial form that
annihilates the digamma jets. -/
def digammaAnnihilator (m : ℕ) : Set (MvPolynomial (Fin m) (RatFunc ℂ)) :=
  {G | ∃ d : Polynomial ℂ, d ≠ 0 ∧ ∃ G' : MvPolynomial (Fin m) (Polynomial ℂ),
    MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) G'
      = MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) d) * G ∧
    AnnihilatesDigamma m G'}

theorem algebraMap_ratFunc_ne_zero {d : Polynomial ℂ} (hd : d ≠ 0) :
    algebraMap (Polynomial ℂ) (RatFunc ℂ) d ≠ 0 := fun h0 =>
  hd (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))

theorem digammaAnnihilator_sub {m : ℕ} (G H : MvPolynomial (Fin m) (RatFunc ℂ))
    (hG : G ∈ digammaAnnihilator m) (hH : H ∈ digammaAnnihilator m) :
    G - H ∈ digammaAnnihilator m := by
  obtain ⟨d₁, hd₁, G', hG', hGv⟩ := hG
  obtain ⟨d₂, hd₂, H', hH', hHv⟩ := hH
  refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂,
    MvPolynomial.C d₂ * G' - MvPolynomial.C d₁ * H', ?_, ?_⟩
  · rw [map_sub, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, hG', hH',
      map_mul, map_mul]
    ring
  · intro z hz
    rw [map_sub, map_mul, map_mul, polyJetEval_C, hGv z hz, hHv z hz,
      mul_zero, mul_zero, sub_zero]

theorem digammaAnnihilator_smul {m : ℕ} (k : RatFunc ℂ)
    (G : MvPolynomial (Fin m) (RatFunc ℂ)) (hG : G ∈ digammaAnnihilator m) :
    MvPolynomial.C k * G ∈ digammaAnnihilator m := by
  obtain ⟨d, hd, G', hG', hGv⟩ := hG
  have hdenK : algebraMap (Polynomial ℂ) (RatFunc ℂ) k.denom ≠ 0 :=
    algebraMap_ratFunc_ne_zero k.denom_ne_zero
  have hnum : algebraMap (Polynomial ℂ) (RatFunc ℂ) k.num
      = k * algebraMap (Polynomial ℂ) (RatFunc ℂ) k.denom :=
    (div_eq_iff hdenK).mp (RatFunc.num_div_denom k)
  refine ⟨d * k.denom, mul_ne_zero hd k.denom_ne_zero,
    MvPolynomial.C k.num * G', ?_, ?_⟩
  · rw [map_mul, MvPolynomial.map_C, hG', hnum]
    simp only [map_mul]
    ring
  · intro z hz
    rw [map_mul, polyJetEval_C, hGv z hz, mul_zero]

theorem digammaAnnihilator_const {m : ℕ} (k : RatFunc ℂ)
    (h : MvPolynomial.C k ∈ digammaAnnihilator m) : k = 0 := by
  obtain ⟨d, hd, G', hG', hGv⟩ := h
  -- the cleared form is a constant
  have hG'C : G' = MvPolynomial.C (MvPolynomial.coeff 0 G') := by
    apply MvPolynomial.ext
    intro β
    rw [MvPolynomial.coeff_C]
    by_cases hβ : 0 = β
    · rw [if_pos hβ, ← hβ]
    · rw [if_neg hβ]
      have hco := congrArg (MvPolynomial.coeff β) hG'
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C,
        if_neg hβ, mul_zero] at hco
      exact RatFunc.algebraMap_injective ℂ (hco.trans (map_zero _).symm)
  -- its constant coefficient vanishes at infinitely many points
  have hpoly : MvPolynomial.coeff 0 G' = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => ((n + 1 : ℕ) : ℂ))
      (fun n₁ n₂ hEq => by
        have h12 : (n₁ + 1 : ℕ) = (n₂ + 1 : ℕ) := Nat.cast_injective hEq
        omega)
    · intro n
      have hne : ∀ p : ℕ, ((n + 1 : ℕ) : ℂ) ≠ -(p : ℂ) := by
        intro p hEq
        have hre := congrArg Complex.re hEq
        push_cast at hre
        have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        simp only [Complex.add_re, Complex.natCast_re, Complex.one_re,
          Complex.neg_re] at hre
        linarith
      have := hGv _ hne
      rw [hG'C, polyJetEval_C] at this
      exact this
  -- hence `toK d · k = 0` with `toK d ≠ 0`
  have h0 := congrArg (MvPolynomial.coeff 0) hG'
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C,
    if_pos rfl, hpoly, map_zero] at h0
  exact (mul_eq_zero.mp h0.symm).resolve_left (algebraMap_ratFunc_ne_zero hd)

/-! ## Shift stability through the cleared substitution -/

/-- The cleared pole numerator `(−1)ʲ·j!·X^{m−1−j}`: the pole part with the denominator
`X^m` cleared. -/
def poleNumerator (m : ℕ) (j : Fin m) : Polynomial ℂ :=
  Polynomial.C (((-1) ^ (j : ℕ) * (j : ℕ).factorial : ℂ))
    * Polynomial.X ^ (m - 1 - (j : ℕ))

theorem poleNumerator_eq (m : ℕ) (j : Fin m) :
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (poleNumerator m j)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X ^ m)
        * polePart (j : ℕ) := by
  rw [poleNumerator, map_mul, map_pow, map_pow, RatFunc.algebraMap_X, algebraMap_polyC,
    polePart]
  have hj : (j : ℕ) + 1 + (m - 1 - (j : ℕ)) = m := by
    have := j.isLt
    omega
  rw [show (RatFunc.X : RatFunc ℂ) ^ m
      = RatFunc.X ^ ((j : ℕ) + 1) * RatFunc.X ^ (m - 1 - (j : ℕ)) by
    rw [← pow_add, hj]]
  have hX1 : (RatFunc.X : RatFunc ℂ) ^ ((j : ℕ) + 1) ≠ 0 :=
    pow_ne_zero _ ratFuncX_ne_zero
  field_simp

/-- The denominator-cleared jet substitution: coefficients shift by one, each jet variable
maps to `X^m·Y_j + (−1)ʲ·j!·X^{m−1−j}`, and each monomial is padded to the uniform clearing
power `X^{m·N}`. -/
def clearedShift (m N : ℕ) (G' : MvPolynomial (Fin m) (Polynomial ℂ)) :
    MvPolynomial (Fin m) (Polynomial ℂ) :=
  ∑ α ∈ G'.support,
    MvPolynomial.C ((MvPolynomial.coeff α G').comp (Polynomial.X + Polynomial.C 1)
        * Polynomial.X ^ (m * (N - degSum α)))
      * ∏ j : Fin m, (MvPolynomial.C (Polynomial.X ^ m) * MvPolynomial.X j
          + MvPolynomial.C (poleNumerator m j)) ^ (α j)

/-- The cleared substitution realizes the jet substitution after clearing `X^{m·N}`. -/
theorem map_clearedShift (m N : ℕ) (G' : MvPolynomial (Fin m) (Polynomial ℂ))
    (hN : G'.totalDegree ≤ N) :
    MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (clearedShift m N G')
      = MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ)
            (Polynomial.X ^ (m * N)))
        * jetTranslate m
            (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) G') := by
  conv_rhs => rw [G'.as_sum]
  rw [map_sum (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))),
    map_sum (jetTranslate m), Finset.mul_sum, clearedShift,
    map_sum (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)))]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hdα : degSum α ≤ N :=
    le_trans (MvPolynomial.le_totalDegree hα) hN
  rw [MvPolynomial.map_monomial, jetTranslate_monomial, ratShift_algebraMap]
  rw [map_mul, MvPolynomial.map_C, map_mul, map_pow]
  -- push the map through the product
  rw [map_prod]
  have hfactor : ∀ j : Fin m,
      MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))
          ((MvPolynomial.C (Polynomial.X ^ m) * MvPolynomial.X j
            + MvPolynomial.C (poleNumerator m j)) ^ (α j))
        = (MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X ^ m))
            * (MvPolynomial.X j + MvPolynomial.C (polePart (j : ℕ)))) ^ (α j) := by
    intro j
    rw [map_pow]
    congr 1
    rw [map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C,
      poleNumerator_eq, map_mul, mul_add]
  rw [Finset.prod_congr rfl fun j _ => hfactor j]
  -- extract the clearing powers
  have hsplit : ∀ j : Fin m,
      (MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X ^ m))
          * (MvPolynomial.X j + MvPolynomial.C (polePart (j : ℕ)))) ^ (α j)
        = MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X ^ m)) ^ (α j)
          * (MvPolynomial.X j + MvPolynomial.C (polePart (j : ℕ))) ^ (α j) := by
    intro j
    rw [mul_pow]
  rw [Finset.prod_congr rfl fun j _ => hsplit j, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  have hpow : (MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X ^ m))
        : MvPolynomial (Fin m) (RatFunc ℂ)) ^ (∑ j : Fin m, α j)
      = MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.X ^ (m * degSum α))) := by
    rw [← map_pow, ← map_pow, ← pow_mul, ← degSum_eq_univ_sum]
  rw [hpow]
  have hexp : m * N = m * (N - degSum α) + m * degSum α := by
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [show (∏ j : Fin m, (MvPolynomial.X j + MvPolynomial.C (polePart (j : ℕ))) ^ (α j)
      : MvPolynomial (Fin m) (RatFunc ℂ)) = transMonomial α from rfl]
  simp only [map_mul, map_pow]
  rw [hexp, pow_add]
  ring

/-- **The value law of the cleared substitution**: evaluation at `z` is `z^{m·N}` times
evaluation at `z + 1`, by the differentiated shift law. -/
theorem polyJetEval_clearedShift {m N : ℕ}
    {G' : MvPolynomial (Fin m) (Polynomial ℂ)} (hN : G'.totalDegree ≤ N)
    {z : ℂ} (hz : ∀ p : ℕ, z ≠ -(p : ℂ)) :
    polyJetEval m z (clearedShift m N G')
      = z ^ (m * N) * polyJetEval m (z + 1) G' := by
  have hz1 : ∀ p : ℕ, z + 1 ≠ -(p : ℂ) := by
    intro p hEq
    exact hz (p + 1) (by push_cast; linear_combination hEq)
  have hz0 : z ≠ 0 := by simpa using hz 0
  -- the key pointwise identity from the shift law
  have hkey : ∀ j : Fin m,
      z ^ m * digammaJet m z j
          + ((-1) ^ (j : ℕ) * ((j : ℕ).factorial : ℂ)) * z ^ (m - 1 - (j : ℕ))
        = z ^ m * digammaJet m (z + 1) j := by
    intro j
    have hFE := digammaJet_shift (j : ℕ) hz
    have hsplit : (z : ℂ) ^ m = z ^ ((j : ℕ) + 1) * z ^ (m - 1 - (j : ℕ)) := by
      rw [← pow_add]
      congr 1
      have := j.isLt
      omega
    rw [digammaJet, digammaJet, hFE, mul_add, hsplit]
    have hzpow : (z : ℂ) ^ ((j : ℕ) + 1) ≠ 0 := pow_ne_zero _ hz0
    field_simp
  -- evaluate the cleared substitution term by term
  rw [clearedShift, map_sum]
  have hterm : ∀ α ∈ G'.support,
      polyJetEval m z
          (MvPolynomial.C ((MvPolynomial.coeff α G').comp
              (Polynomial.X + Polynomial.C 1)
            * Polynomial.X ^ (m * (N - degSum α)))
          * ∏ j : Fin m, (MvPolynomial.C (Polynomial.X ^ m) * MvPolynomial.X j
              + MvPolynomial.C (poleNumerator m j)) ^ (α j))
        = z ^ (m * N) * ((MvPolynomial.coeff α G').eval (z + 1)
            * ∏ j : Fin m, digammaJet m (z + 1) j ^ (α j)) := by
    intro α hα
    have hdα : degSum α ≤ N := le_trans (MvPolynomial.le_totalDegree hα) hN
    rw [map_mul, polyJetEval_C, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    rw [map_prod]
    have hfac : ∀ j : Fin m,
        polyJetEval m z ((MvPolynomial.C (Polynomial.X ^ m) * MvPolynomial.X j
            + MvPolynomial.C (poleNumerator m j)) ^ (α j))
          = (z ^ m * digammaJet m (z + 1) j) ^ (α j) := by
      intro j
      rw [map_pow]
      congr 1
      rw [map_add, map_mul, polyJetEval_C, polyJetEval_C]
      rw [show polyJetEval m z (MvPolynomial.X j) = digammaJet m z j from
        eval₂Hom_X' _ _ _]
      rw [Polynomial.eval_pow, Polynomial.eval_X, poleNumerator, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      exact hkey j
    rw [Finset.prod_congr rfl fun j _ => hfac j]
    have hpull : ∏ j : Fin m, (z ^ m * digammaJet m (z + 1) j) ^ (α j)
        = z ^ (m * degSum α) * ∏ j : Fin m, digammaJet m (z + 1) j ^ (α j) := by
      rw [Finset.prod_congr rfl fun j _ => mul_pow _ _ _, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, ← pow_mul, ← degSum_eq_univ_sum, Nat.mul_comm]
    rw [hpull]
    have hcombine : (z : ℂ) ^ (m * (N - degSum α)) * z ^ (m * degSum α)
        = z ^ (m * N) := by
      rw [← pow_add]
      congr 1
      rw [← Nat.mul_add]
      congr 1
      omega
    calc (MvPolynomial.coeff α G').eval (z + 1) * z ^ (m * (N - degSum α))
          * (z ^ (m * degSum α) * ∏ j : Fin m, digammaJet m (z + 1) j ^ (α j))
        = (z ^ (m * (N - degSum α)) * z ^ (m * degSum α))
            * ((MvPolynomial.coeff α G').eval (z + 1)
              * ∏ j : Fin m, digammaJet m (z + 1) j ^ (α j)) := by ring
      _ = z ^ (m * N) * ((MvPolynomial.coeff α G').eval (z + 1)
              * ∏ j : Fin m, digammaJet m (z + 1) j ^ (α j)) := by rw [hcombine]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hexpand : polyJetEval m (z + 1) G'
      = ∑ α ∈ G'.support, (MvPolynomial.coeff α G').eval (z + 1)
          * ∏ j : Fin m, digammaJet m (z + 1) j ^ (α j) := by
    have hcast : polyJetEval m (z + 1) G'
        = eval₂ (Polynomial.evalRingHom (z + 1)) (digammaJet m (z + 1)) G' := rfl
    rw [hcast, eval₂_eq']
    rfl
  rw [← hexpand]

/-- The cleared substitution preserves annihilation. -/
theorem annihilatesDigamma_clearedShift {m N : ℕ}
    {G' : MvPolynomial (Fin m) (Polynomial ℂ)} (hN : G'.totalDegree ≤ N)
    (hGv : AnnihilatesDigamma m G') :
    AnnihilatesDigamma m (clearedShift m N G') := by
  intro z hz
  have hz1 : ∀ p : ℕ, z + 1 ≠ -(p : ℂ) := by
    intro p hEq
    exact hz (p + 1) (by push_cast; linear_combination hEq)
  rw [polyJetEval_clearedShift hN hz, hGv (z + 1) hz1, mul_zero]

/-- The annihilator set is stable under the jet substitution. -/
theorem digammaAnnihilator_shift {m : ℕ} (G : MvPolynomial (Fin m) (RatFunc ℂ))
    (hG : G ∈ digammaAnnihilator m) : jetTranslate m G ∈ digammaAnnihilator m := by
  obtain ⟨d, hd, G', hG', hGv⟩ := hG
  refine ⟨Polynomial.X ^ (m * G'.totalDegree) * d.comp (Polynomial.X + Polynomial.C 1),
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (comp_X_add_C_one_ne_zero hd),
    clearedShift m G'.totalDegree G', ?_,
    annihilatesDigamma_clearedShift le_rfl hGv⟩
  rw [map_clearedShift m G'.totalDegree G' le_rfl, hG', map_mul (jetTranslate m),
    jetTranslate_C, ratShift_algebraMap, map_mul, map_mul]
  ring

/-! ## Hölder's theorem for `ψ` -/

/-- **Off-pole jet annihilators of digamma vanish**: a differential polynomial whose
evaluation on the digamma jets vanishes off the poles `−ℕ` is the zero polynomial — the
polynomial-level form of Hölder's theorem, with vanishing required only where `ψ` is
defined. -/
theorem digamma_jet_annihilator_eq_zero (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ)
    (hPz : ∀ z : ℂ, (∀ p : ℕ, z ≠ -(p : ℂ)) →
      MvPolynomial.eval (Fin.cons z fun j : Fin (n + 1) =>
        iteratedDeriv (j : ℕ) Complex.digamma z) P = 0) : P = 0 := by
  by_contra hP0
  set G' := reshapeJet n P with hG'_def
  have hG'0 : G' ≠ 0 := fun h0 =>
    hP0 (reshapeJet_injective n (by rw [← hG'_def, h0, map_zero]))
  have hG'v : AnnihilatesDigamma (n + 1) G' := by
    intro z hz
    rw [hG'_def, polyJetEval_reshapeJet]
    exact hPz z hz
  refine no_shift_stable_annihilator (digammaAnnihilator (n + 1))
    (fun G H hG hH => digammaAnnihilator_sub G H hG hH)
    (fun k G hG => digammaAnnihilator_smul k G hG)
    (fun G hG => digammaAnnihilator_shift G hG)
    (fun k hk => digammaAnnihilator_const k hk)
    ⟨MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) G',
      ⟨1, one_ne_zero, G', by rw [map_one, MvPolynomial.C_1, one_mul], hG'v⟩, ?_⟩
  intro h0
  exact hG'0 (MvPolynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)
    (by rw [h0, map_zero]))

/-- **The digamma function is hypertranscendental** (Hölder's theorem, digamma form):
`ψ = Γ'/Γ` satisfies no algebraic differential equation over `ℂ[s]`.  Machine-checked by
shift elimination: a minimal annihilator would have shift-periodic top coefficients and
difference equations with single-orbit poles one layer below, forcing the gradient of its
top form to vanish — impossible in characteristic zero. -/
theorem hypertranscendental_digamma : Hypertranscendental Complex.digamma := by
  rintro ⟨n, P, hP0, hPz⟩
  exact hP0 (digamma_jet_annihilator_eq_zero n P (fun z _ => hPz z))

/-! ## The polynomial-coefficient annihilator theorem -/

theorem reshapeJet_comp_reshapeJetInv (n : ℕ) :
    (reshapeJet n).comp (reshapeJetInv n) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro p
    have hext : ((reshapeJet n).comp (reshapeJetInv n)).comp
          (MvPolynomial.C : Polynomial ℂ →+* MvPolynomial (Fin (n + 1)) (Polynomial ℂ))
        = (MvPolynomial.C : Polynomial ℂ →+* MvPolynomial (Fin (n + 1)) (Polynomial ℂ))
        := by
      apply Polynomial.ringHom_ext
      · intro a
        simp [reshapeJet, reshapeJetInv]
      · simp [reshapeJet, reshapeJetInv]
    have := RingHom.congr_fun hext p
    simpa using this
  · intro j
    simp [reshapeJet, reshapeJetInv]

theorem reshapeJetInv_injective (n : ℕ) : Function.Injective (reshapeJetInv n) := by
  intro a b h
  have ha := RingHom.congr_fun (reshapeJet_comp_reshapeJetInv n) a
  have hb := RingHom.congr_fun (reshapeJet_comp_reshapeJetInv n) b
  rw [RingHom.comp_apply] at ha hb
  rw [RingHom.id_apply] at ha hb
  rw [← ha, ← hb, h]

theorem poly_eval_offPole_eq_zero {p : Polynomial ℂ}
    (h : ∀ z : ℂ, (∀ q : ℕ, z ≠ -(q : ℂ)) → p.eval z = 0) : p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((n + 1 : ℕ) : ℂ))
    (fun n₁ n₂ hEq => by
      have h12 : (n₁ + 1 : ℕ) = (n₂ + 1 : ℕ) := Nat.cast_injective hEq
      omega)
  intro n
  have hne : ∀ q : ℕ, ((n + 1 : ℕ) : ℂ) ≠ -(q : ℂ) := by
    intro q hEq
    have hre := congrArg Complex.re hEq
    push_cast at hre
    have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re,
      Complex.neg_re] at hre
    linarith
  exact h _ hne

/-- **The polynomial-coefficient annihilator theorem**: a polynomial-coefficient jet
polynomial whose evaluation on the digamma jets vanishes off the poles is zero — the
coefficient-ring form of Hölder's theorem, consumed by the Γ-power elimination. -/
theorem polyJetEval_offPole_eq_zero {m : ℕ}
    (G : MvPolynomial (Fin m) (Polynomial ℂ))
    (hG : ∀ z : ℂ, (∀ p : ℕ, z ≠ -(p : ℂ)) → polyJetEval m z G = 0) : G = 0 := by
  cases m with
  | zero =>
      obtain ⟨p, rfl⟩ := MvPolynomial.C_surjective (Fin 0) G
      rw [show (0 : MvPolynomial (Fin 0) (Polynomial ℂ)) = MvPolynomial.C 0 by
        rw [map_zero]]
      congr 1
      apply poly_eval_offPole_eq_zero
      intro z hz
      have := hG z hz
      rwa [polyJetEval_C] at this
  | succ n =>
      have hvan : ∀ z : ℂ, (∀ p : ℕ, z ≠ -(p : ℂ)) →
          MvPolynomial.eval (Fin.cons z fun j : Fin (n + 1) =>
            iteratedDeriv (j : ℕ) Complex.digamma z) (reshapeJetInv n G) = 0 := by
        intro z hz
        rw [← polyJetEval_reshapeJet]
        rw [show reshapeJet n (reshapeJetInv n G) = G from
          RingHom.congr_fun (reshapeJet_comp_reshapeJetInv n) G]
        exact hG z hz
      have h0 := digamma_jet_annihilator_eq_zero n (reshapeJetInv n G) hvan
      have := congrArg (reshapeJet n) h0
      rwa [show reshapeJet n (reshapeJetInv n G) = G from
        RingHom.congr_fun (reshapeJet_comp_reshapeJetInv n) G, map_zero] at this

end GaloisForLFunctions

end
