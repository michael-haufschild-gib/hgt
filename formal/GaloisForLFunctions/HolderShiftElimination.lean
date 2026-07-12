import GaloisForLFunctions.HolderDifferenceBricks
import GaloisForLFunctions.DifferentialIndependence

/-!
# Shift elimination over rational functions: the engine of Hölder's theorem

The classical difference-equation proof of Hölder's theorem eliminates a hypothetical
algebraic differential equation for the digamma function `ψ` against the shift law
`ψ⁽ʲ⁾(s+1) = ψ⁽ʲ⁾(s) + (−1)ʲ·j!/s^{j+1}`.  This module executes the entire elimination as
commutative algebra over the rational-function field `K = ℂ(X)`:

* `ratShift` — the unit-shift field endomorphism `r(X) ↦ r(X+1)` of `RatFunc ℂ`;
  `ratShift_fixed_eq_const` upgrades the shift-periodic brick to `K`: a shift-invariant
  rational function is a constant.
* `polePart j = (−1)ʲ·j!/X^{j+1}` — the shift increments of the digamma jets;
  `ratShift_sub_polePart_combination` upgrades the single-pole brick: no rational function
  has a shift increment in the span of the pole parts.
* `jetTranslate` — the substitution `a(X) ↦ a(X+1)`, `Y_j ↦ Y_j + polePart j` on
  `MvPolynomial (Fin m) K`, the exact transformation law of the digamma jet vector under
  `s ↦ s+1`.  Its action is unipotent-triangular for the total degree in the jet
  variables: the top coefficient layer maps by `ratShift`
  (`coeff_jetTranslate_of_le_degSum`), and the next layer picks up the gradient term
  `Σ (β_j+1)·polePart j·ratShift(top)` (`coeff_jetTranslate_of_le_degSum_succ`).
* `no_shift_stable_annihilator` — **the elimination theorem**: no nonzero
  shift-stable annihilator space exists.  A subset of `MvPolynomial (Fin m) K` closed
  under subtraction, `K`-scalars, and `jetTranslate`, containing no nonzero constant,
  contains no nonzero element at all.  A double-minimal element (minimal jet degree, then
  minimal top-layer support) forces `jetTranslate P = u·P`; the top layer is then
  shift-periodic, hence constant; the next layer satisfies difference equations with
  single-orbit poles, killing the gradient of the top form — impossible in characteristic
  zero.
-/

noncomputable section

namespace GaloisForLFunctions

/-! ## The shift automorphism of `ℂ(X)` -/

section RatShift

open Polynomial nonZeroDivisors

theorem comp_X_add_C_one_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0) :
    p.comp (X + C 1) ≠ 0 := by
  intro h0
  exact hp ((Polynomial.comp_eq_zero_iff.mp h0).resolve_right
    (fun hh => by simpa using hh.2))

/-- The unit shift `p(X) ↦ p(X+1)` on polynomials, valued in the rational-function field. -/
def shiftCompHom : Polynomial ℂ →+* RatFunc ℂ :=
  (algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp
    (Polynomial.eval₂RingHom Polynomial.C (X + C 1))

theorem shiftCompHom_apply (p : Polynomial ℂ) :
    shiftCompHom p = algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (X + C 1)) := rfl

theorem shiftCompHom_mem_nonZeroDivisors :
    (Polynomial ℂ)⁰ ≤ (RatFunc ℂ)⁰.comap shiftCompHom := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  rw [shiftCompHom_apply]
  intro h0
  exact comp_X_add_C_one_ne_zero hp
    (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))

/-- The unit-shift endomorphism `r(X) ↦ r(X+1)` of the rational-function field. -/
def ratShift : RatFunc ℂ →+* RatFunc ℂ :=
  RatFunc.liftRingHom shiftCompHom shiftCompHom_mem_nonZeroDivisors

theorem ratShift_algebraMap (p : Polynomial ℂ) :
    ratShift (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (X + C 1)) := by
  have h := RatFunc.liftRingHom_apply_div shiftCompHom
    shiftCompHom_mem_nonZeroDivisors p 1
  simp only [map_one, div_one] at h
  exact h

theorem algebraMap_polyC (c : ℂ) :
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c)
      = algebraMap ℂ (RatFunc ℂ) c := by
  rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

theorem ratShift_injective : Function.Injective ratShift :=
  ratShift.injective

theorem ratShift_const (t : ℂ) :
    ratShift (algebraMap ℂ (RatFunc ℂ) t) = algebraMap ℂ (RatFunc ℂ) t := by
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ) t,
    Polynomial.algebraMap_eq, ratShift_algebraMap, Polynomial.C_comp]

/-- **Shift-invariant rational functions are constant.**  The rational-function form of the
shift-periodic quotient brick: `r(X+1) = r(X)` in `ℂ(X)` forces `r ∈ ℂ`. -/
theorem ratShift_fixed_eq_const {r : RatFunc ℂ} (h : ratShift r = r) :
    ∃ t : ℂ, r = algebraMap ℂ (RatFunc ℂ) t := by
  set p := r.num with hp_def
  set q := r.denom with hq_def
  have hq : q ≠ 0 := r.denom_ne_zero
  have hco : IsCoprime p q := r.isCoprime_num_denom
  have hr : algebraMap (Polynomial ℂ) (RatFunc ℂ) p
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) q = r := RatFunc.num_div_denom r
  have hqK : algebraMap (Polynomial ℂ) (RatFunc ℂ) q ≠ 0 := fun h0 =>
    hq (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hqcK : algebraMap (Polynomial ℂ) (RatFunc ℂ) (q.comp (X + C 1)) ≠ 0 := fun h0 =>
    comp_X_add_C_one_ne_zero hq (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hshift : algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (X + C 1))
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) (q.comp (X + C 1)) = r := by
    rw [← ratShift_algebraMap, ← ratShift_algebraMap, ← map_div₀, hr, h]
  have hcross : p.comp (X + C 1) * q = p * q.comp (X + C 1) := by
    apply RatFunc.algebraMap_injective ℂ
    have h2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (X + C 1))
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) (q.comp (X + C 1))
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) p
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) q := by
      rw [hshift, hr]
    rw [div_eq_div_iff hqcK hqK] at h2
    rw [map_mul, map_mul]
    linear_combination h2
  obtain ⟨a, b, hpa, hqb⟩ := shift_periodic_quotient_constant hco hcross
  have hb : b ≠ 0 := fun h0 => hq (by rw [hqb, h0, map_zero])
  refine ⟨a / b, ?_⟩
  rw [← hr, hpa, hqb, algebraMap_polyC, algebraMap_polyC, ← map_div₀]

/-! ## The digamma pole parts and the single-orbit-pole brick over `ℂ(X)` -/

/-- The shift increment of the `j`-th digamma jet: `polePart j = (−1)ʲ·j!/X^{j+1}`. -/
def polePart (j : ℕ) : RatFunc ℂ :=
  algebraMap ℂ (RatFunc ℂ) ((-1) ^ j * j.factorial) / RatFunc.X ^ (j + 1)

theorem ratFuncX_ne_zero : (RatFunc.X : RatFunc ℂ) ≠ 0 := by
  rw [← RatFunc.algebraMap_X]
  exact fun h0 => Polynomial.X_ne_zero (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))

/-- **No rational function has a shift increment in the span of the pole parts.**  If
`r(X+1) − r(X) = Σ_j δ_j·polePart j` then every `δ_j = 0`: the rational-function form of the
single-orbit-pole brick, obtained by cross-multiplying against `num/denom` and pinching the
extreme integer roots of the denominator. -/
theorem ratShift_sub_polePart_combination {m : ℕ} {w : RatFunc ℂ} {δ : Fin m → ℂ}
    (h : ratShift w - w
      = ∑ j : Fin m, algebraMap ℂ (RatFunc ℂ) (δ j) * polePart (j : ℕ)) :
    ∀ j, δ j = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact fun j => absurd j.isLt (by omega)
  set p := w.num with hp_def
  set q := w.denom with hq_def
  have hq : q ≠ 0 := w.denom_ne_zero
  have hco : IsCoprime p q := w.isCoprime_num_denom
  set A : Polynomial ℂ :=
    ∑ j : Fin m, Polynomial.C (δ j * ((-1) ^ (j : ℕ) * (j : ℕ).factorial))
      * X ^ (m - 1 - (j : ℕ)) with hA_def
  -- the combination of pole parts is `A/X^m`
  have hcomb : ∑ j : Fin m, algebraMap ℂ (RatFunc ℂ) (δ j) * polePart (j : ℕ)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) A
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (X ^ m) := by
    rw [hA_def, map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (j : ℕ) + 1 + (m - 1 - (j : ℕ)) = m := by omega
    have hRHSnum : algebraMap (Polynomial ℂ) (RatFunc ℂ)
          (Polynomial.C (δ j * ((-1) ^ (j : ℕ) * (j : ℕ).factorial)) * X ^ (m - 1 - (j : ℕ)))
        = algebraMap ℂ (RatFunc ℂ) (δ j * ((-1) ^ (j : ℕ) * (j : ℕ).factorial))
            * RatFunc.X ^ (m - 1 - (j : ℕ)) := by
      rw [map_mul, map_pow, RatFunc.algebraMap_X, algebraMap_polyC]
    have hRHSden : algebraMap (Polynomial ℂ) (RatFunc ℂ) ((X : Polynomial ℂ) ^ m)
        = (RatFunc.X : RatFunc ℂ) ^ ((j : ℕ) + 1) * RatFunc.X ^ (m - 1 - (j : ℕ)) := by
      rw [map_pow, RatFunc.algebraMap_X, ← pow_add, hj]
    rw [hRHSnum, hRHSden, polePart]
    have hX1 : (RatFunc.X : RatFunc ℂ) ^ ((j : ℕ) + 1) ≠ 0 :=
      pow_ne_zero _ ratFuncX_ne_zero
    have hX2 : (RatFunc.X : RatFunc ℂ) ^ (m - 1 - (j : ℕ)) ≠ 0 :=
      pow_ne_zero _ ratFuncX_ne_zero
    rw [map_mul]
    field_simp
    rw [← map_mul, ← map_mul]
    congr 1
    ring
  -- cross-multiplied polynomial identity
  have hqK : algebraMap (Polynomial ℂ) (RatFunc ℂ) q ≠ 0 := fun h0 =>
    hq (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hqcK : algebraMap (Polynomial ℂ) (RatFunc ℂ) (q.comp (X + C 1)) ≠ 0 := fun h0 =>
    comp_X_add_C_one_ne_zero hq (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hXK : algebraMap (Polynomial ℂ) (RatFunc ℂ) ((X : Polynomial ℂ) ^ m) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ fun h0 =>
      Polynomial.X_ne_zero (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hw : algebraMap (Polynomial ℂ) (RatFunc ℂ) p
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) q = w := RatFunc.num_div_denom w
  have hshiftw : ratShift w = algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (X + C 1))
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) (q.comp (X + C 1)) := by
    rw [← hw, map_div₀, ratShift_algebraMap, ratShift_algebraMap]
  have hcross : (X : Polynomial ℂ) ^ ((m - 1) + 1)
      * (p.comp (X + C 1) * q - p * q.comp (X + C 1)) = A * (q * q.comp (X + C 1)) := by
    apply RatFunc.algebraMap_injective ℂ
    have hm1 : (m - 1) + 1 = m := by omega
    rw [hm1, map_mul, map_mul, map_mul, map_sub, map_mul, map_mul]
    rw [hcomb, hshiftw, ← hw] at h
    field_simp at h
    linear_combination h
  have hA0 : A = 0 :=
    difference_single_pole_free hq hco
      (by
        rw [hA_def]
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
        refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [Polynomial.natDegree_X_pow]
        omega)
      hcross
  -- coefficient extraction
  intro j
  have hcoeff := congrArg (fun B => Polynomial.coeff B (m - 1 - (j : ℕ))) hA0
  simp only [hA_def, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single j (fun k _ hk => by
      rw [if_neg (fun hEq => hk (by
        have hkm : (k : ℕ) < m := k.isLt
        have hjm : (j : ℕ) < m := j.isLt
        have : (k : ℕ) = (j : ℕ) := by omega
        exact Fin.ext this)), mul_zero])
    (fun hj => absurd (Finset.mem_univ j) hj)] at hcoeff
  rw [if_pos rfl, mul_one] at hcoeff
  have hfac : ((-1 : ℂ) ^ (j : ℕ) * (j : ℕ).factorial) ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · exact_mod_cast Nat.factorial_ne_zero (j : ℕ)
  exact (mul_eq_zero.mp hcoeff).resolve_right hfac

end RatShift

/-! ## The jet substitution on `MvPolynomial (Fin m) ℂ(X)` -/

section Jet

open MvPolynomial

variable {m : ℕ}

/-- Total degree of a monomial exponent in the jet variables. -/
def degSum (α : Fin m →₀ ℕ) : ℕ := α.sum fun _ e => e

theorem degSum_add (α β : Fin m →₀ ℕ) : degSum (α + β) = degSum α + degSum β :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem degSum_single (j : Fin m) (k : ℕ) : degSum (Finsupp.single j k) = k :=
  Finsupp.sum_single_index rfl

theorem degSum_zero : degSum (0 : Fin m →₀ ℕ) = 0 :=
  Finsupp.sum_zero_index

theorem degSum_eq_univ_sum (α : Fin m →₀ ℕ) : degSum α = ∑ j : Fin m, α j :=
  Finsupp.sum_fintype _ _ (fun _ => rfl)

theorem totalDegree_eq_sup_degSum (P : MvPolynomial (Fin m) (RatFunc ℂ)) :
    P.totalDegree = P.support.sup degSum := rfl

theorem exists_apply_ne_zero_of_degSum_pos {α : Fin m →₀ ℕ} (h : 0 < degSum α) :
    ∃ j, α j ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have : α = 0 := Finsupp.ext hall
  rw [this, degSum_zero] at h
  omega

theorem sub_single_add_single {α : Fin m →₀ ℕ} {j : Fin m} (h : α j ≠ 0) :
    α - Finsupp.single j 1 + Finsupp.single j 1 = α := by
  ext k
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases hk : j = k
  · subst hk
    rw [if_pos rfl]
    omega
  · rw [if_neg hk]
    omega

theorem degSum_sub_single {α : Fin m →₀ ℕ} {j : Fin m} (h : α j ≠ 0) :
    degSum (α - Finsupp.single j 1) + 1 = degSum α := by
  conv_rhs => rw [← sub_single_add_single h]
  rw [degSum_add, degSum_single]

theorem add_single_sub_single (α : Fin m →₀ ℕ) (j : Fin m) :
    α + Finsupp.single j 1 - Finsupp.single j 1 = α := by
  ext k
  simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases hk : j = k
  · subst hk
    rw [if_pos rfl]
    omega
  · rw [if_neg hk]
    omega

/-- The jet substitution: coefficients shift by `ratShift`, each jet variable translates by
its pole part — the transformation law of the digamma jet vector under `s ↦ s+1`. -/
def jetTranslate (m : ℕ) :
    MvPolynomial (Fin m) (RatFunc ℂ) →+* MvPolynomial (Fin m) (RatFunc ℂ) :=
  ((mvPolynomialBaseTranslation
      (fun j : Fin m => polePart (j : ℕ))).toAlgHom.toRingHom).comp
    (MvPolynomial.map ratShift)

theorem jetTranslate_C (k : RatFunc ℂ) :
    jetTranslate m (C k) = C (ratShift k) := by
  unfold jetTranslate
  rw [RingHom.comp_apply, MvPolynomial.map_C]
  rw [show (C (ratShift k) : MvPolynomial (Fin m) (RatFunc ℂ))
      = algebraMap (RatFunc ℂ) (MvPolynomial (Fin m) (RatFunc ℂ)) (ratShift k) from rfl]
  exact (mvPolynomialBaseTranslation _).commutes _

theorem jetTranslate_X (j : Fin m) :
    jetTranslate m (X j) = X j + C (polePart (j : ℕ)) := by
  unfold jetTranslate
  rw [RingHom.comp_apply, MvPolynomial.map_X]
  exact mvPolynomialBaseTranslation_X _ j

/-- The translated monomial `Π_j (Y_j + polePart j)^{α_j}`. -/
def transMonomial (α : Fin m →₀ ℕ) : MvPolynomial (Fin m) (RatFunc ℂ) :=
  ∏ j : Fin m, (X j + C (polePart (j : ℕ))) ^ (α j)

theorem jetTranslate_monomial (α : Fin m →₀ ℕ) (a : RatFunc ℂ) :
    jetTranslate m (monomial α a) = C (ratShift a) * transMonomial α := by
  rw [MvPolynomial.monomial_eq, map_mul]
  congr 1
  · exact jetTranslate_C a
  · rw [Finsupp.prod_fintype _ _ (fun j => pow_zero _), map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_pow, jetTranslate_X]

theorem transMonomial_zero : transMonomial (0 : Fin m →₀ ℕ) = 1 := by
  unfold transMonomial
  refine Finset.prod_eq_one fun j _ => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply, pow_zero]

theorem transMonomial_add_single (α : Fin m →₀ ℕ) (j : Fin m) :
    transMonomial (α + Finsupp.single j 1)
      = transMonomial α * (X j + C (polePart (j : ℕ))) := by
  unfold transMonomial
  rw [Finset.prod_congr rfl (fun k _ => by rw [Finsupp.add_apply, pow_add]),
    Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single j
    (fun k _ hk => by
      rw [Finsupp.single_apply, if_neg (fun h => hk (Eq.symm h)), pow_zero])
    (fun h => absurd (Finset.mem_univ j) h)]
  rw [Finsupp.single_apply, if_pos rfl, pow_one]

/-- The subtop layer of a translated monomial: `Σ_j α_j·polePart j·Y^{α − e_j}`. -/
def subTopMonomial (α : Fin m →₀ ℕ) : MvPolynomial (Fin m) (RatFunc ℂ) :=
  ∑ j : Fin m,
    monomial (α - Finsupp.single j 1) ((α j : RatFunc ℂ) * polePart (j : ℕ))

theorem subTopMonomial_zero : subTopMonomial (0 : Fin m →₀ ℕ) = 0 := by
  unfold subTopMonomial
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_mul, map_zero]

theorem X_eq_monomial (j : Fin m) :
    (X j : MvPolynomial (Fin m) (RatFunc ℂ)) = monomial (Finsupp.single j 1) 1 := rfl

theorem subTopMonomial_add_single (α : Fin m →₀ ℕ) (j : Fin m) :
    subTopMonomial (α + Finsupp.single j 1)
      = subTopMonomial α * X j + C (polePart (j : ℕ)) * monomial α 1 := by
  unfold subTopMonomial
  rw [Finset.sum_mul]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _
      (fun k => monomial (α - Finsupp.single k 1) ((α k : RatFunc ℂ) * polePart (k : ℕ))
        * X j) (Finset.mem_univ j), add_assoc]
  congr 1
  · -- off-`j` terms match after commuting the added unit past the removed one
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    rw [X_eq_monomial, monomial_mul, mul_one]
    have happ : ((α + Finsupp.single j 1 : Fin m →₀ ℕ)) k = α k := by
      rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (fun h => hkj (Eq.symm h)),
        add_zero]
    rw [happ]
    have hidx : (α + Finsupp.single j 1 : Fin m →₀ ℕ) - Finsupp.single k 1
        = α - Finsupp.single k 1 + Finsupp.single j 1 := by
      ext l
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    rw [hidx]
  · -- the `j` term absorbs the extra `C (polePart j) * monomial α 1`
    rw [X_eq_monomial, monomial_mul, mul_one, add_single_sub_single]
    have happ : ((α + Finsupp.single j 1 : Fin m →₀ ℕ)) j = α j + 1 := by
      rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl]
    rw [happ]
    have hCmul : C (polePart (j : ℕ)) * (monomial α 1 : MvPolynomial (Fin m) (RatFunc ℂ))
        = monomial α (polePart (j : ℕ)) := by
      rw [MvPolynomial.C_mul_monomial, mul_one]
    rw [hCmul]
    by_cases hα : α j = 0
    · rw [hα, Nat.cast_zero, zero_mul, map_zero, zero_add, Nat.cast_one, one_mul]
      rw [zero_add]
    · rw [sub_single_add_single hα]
      rw [show ((α j + 1 : ℕ) : RatFunc ℂ) = (α j : RatFunc ℂ) + 1 by push_cast; ring]
      rw [add_mul, one_mul, map_add]

/-- **Layer decomposition of a translated monomial.**  `Π (Y_j + c_j)^{α_j}` is the original
monomial, plus the gradient layer `Σ_j α_j·c_j·Y^{α−e_j}`, plus an error supported in
degrees at most `degSum α − 2`. -/
theorem transMonomial_decomposition (α : Fin m →₀ ℕ) :
    ∃ E : MvPolynomial (Fin m) (RatFunc ℂ),
      transMonomial α = monomial α 1 + subTopMonomial α + E ∧
      ∀ β : Fin m →₀ ℕ, degSum α ≤ degSum β + 1 → coeff β E = 0 := by
  generalize hN : degSum α = N
  induction N using Nat.strong_induction_on generalizing α with
  | _ N ih =>
    rcases eq_or_ne α 0 with rfl | hα0
    · refine ⟨0, ?_, fun β _ => coeff_zero β⟩
      rw [transMonomial_zero, subTopMonomial_zero, add_zero, add_zero]
      rw [show (monomial (0 : Fin m →₀ ℕ) (1 : RatFunc ℂ)) = C 1 from (C_apply).symm, map_one]
    · have hpos : 0 < degSum α := by
        rcases Nat.eq_zero_or_pos (degSum α) with h0 | h
        · exfalso
          apply hα0
          ext k
          have hk : α k ≤ degSum α := by
            rw [degSum_eq_univ_sum]
            exact Finset.single_le_sum (f := fun k => α k) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ k)
          simp only [Finsupp.coe_zero, Pi.zero_apply]
          omega
        · exact h
      obtain ⟨j, hj⟩ := exists_apply_ne_zero_of_degSum_pos hpos
      set α' := α - Finsupp.single j 1 with hα'_def
      have hres : α' + Finsupp.single j 1 = α := sub_single_add_single hj
      have hdeg' : degSum α' + 1 = degSum α := degSum_sub_single hj
      obtain ⟨E', hE'eq, hE'coeff⟩ := ih (degSum α') (by omega) α' rfl
      refine ⟨C (polePart (j : ℕ)) * subTopMonomial α'
        + E' * (X j + C (polePart (j : ℕ))), ?_, ?_⟩
      · rw [← hres, transMonomial_add_single, hE'eq, subTopMonomial_add_single,
          show (monomial (α' + Finsupp.single j 1) (1 : RatFunc ℂ))
              = monomial α' 1 * X j by
            rw [X_eq_monomial, monomial_mul, mul_one]]
        ring
      · intro β hβ
        rw [← hN, ← hdeg'] at hβ
        have h1 : coeff β (C (polePart (j : ℕ)) * subTopMonomial α') = 0 := by
          rw [coeff_C_mul]
          have hsub : coeff β (subTopMonomial α') = 0 := by
            unfold subTopMonomial
            rw [coeff_sum]
            refine Finset.sum_eq_zero fun k _ => ?_
            by_cases hk : α' k = 0
            · rw [hk, Nat.cast_zero, zero_mul, map_zero, coeff_zero]
            · rw [coeff_monomial]
              refine if_neg fun hEq => ?_
              have hlt := degSum_sub_single hk
              rw [hEq] at hlt
              omega
          rw [hsub, mul_zero]
        have h2 : coeff β (E' * (X j + C (polePart (j : ℕ)))) = 0 := by
          rw [mul_add, coeff_add]
          have h2a : coeff β (E' * X j) = 0 := by
            rw [coeff_mul_X']
            by_cases hmem : j ∈ β.support
            · rw [if_pos hmem]
              refine hE'coeff _ ?_
              have hdegβ := degSum_sub_single (Finsupp.mem_support_iff.mp hmem)
              omega
            · rw [if_neg hmem]
          have h2b : coeff β (E' * C (polePart (j : ℕ))) = 0 := by
            rw [mul_comm, coeff_C_mul, hE'coeff β (by omega), mul_zero]
          rw [h2a, h2b, add_zero]
        rw [coeff_add, h1, h2, add_zero]

theorem coeff_transMonomial_of_degSum_eq {α β : Fin m →₀ ℕ}
    (h : degSum β = degSum α) :
    coeff β (transMonomial α) = if α = β then 1 else 0 := by
  obtain ⟨E, hEq, hE⟩ := transMonomial_decomposition α
  rw [hEq, coeff_add, coeff_add, coeff_monomial]
  have h1 : coeff β (subTopMonomial α) = 0 := by
    unfold subTopMonomial
    rw [coeff_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : α k = 0
    · rw [hk, Nat.cast_zero, zero_mul, map_zero, coeff_zero]
    · rw [coeff_monomial]
      refine if_neg fun hEq' => ?_
      have hlt := degSum_sub_single hk
      rw [hEq'] at hlt
      omega
  rw [h1, hE β (by omega), add_zero, add_zero]

theorem coeff_transMonomial_of_degSum_succ {α β : Fin m →₀ ℕ}
    (h : degSum β + 1 = degSum α) :
    coeff β (transMonomial α)
      = ∑ j : Fin m, if α = β + Finsupp.single j 1
          then (α j : RatFunc ℂ) * polePart (j : ℕ) else 0 := by
  obtain ⟨E, hEq, hE⟩ := transMonomial_decomposition α
  rw [hEq, coeff_add, coeff_add, coeff_monomial,
    if_neg (fun hEq' => by rw [hEq'] at h; omega), hE β (by omega), zero_add, add_zero]
  unfold subTopMonomial
  rw [coeff_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_monomial]
  by_cases hj : α j = 0
  · rw [if_neg, if_neg]
    · intro hEq'
      have : ((β + Finsupp.single j 1 : Fin m →₀ ℕ)) j = α j := by rw [← hEq']
      rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl] at this
      omega
    · intro hEq'
      have : α - Finsupp.single j 1 = α := by
        ext l
        simp only [Finsupp.tsub_apply, Finsupp.single_apply]
        by_cases hl : j = l
        · subst hl; omega
        · rw [if_neg hl]; omega
      rw [this] at hEq'
      rw [hEq'] at h
      omega
  · have hiff : (α - Finsupp.single j 1 = β) ↔ (α = β + Finsupp.single j 1) := by
      constructor
      · intro hEq'
        rw [← hEq', sub_single_add_single hj]
      · intro hEq'
        rw [hEq', add_single_sub_single]
    by_cases hcase : α = β + Finsupp.single j 1
    · rw [if_pos (hiff.mpr hcase), if_pos hcase]
    · rw [if_neg (fun h' => hcase (hiff.mp h')), if_neg hcase]

theorem coeff_transMonomial_of_degSum_lt {α β : Fin m →₀ ℕ}
    (h : degSum α < degSum β) :
    coeff β (transMonomial α) = 0 := by
  obtain ⟨E, hEq, hE⟩ := transMonomial_decomposition α
  rw [hEq, coeff_add, coeff_add, coeff_monomial,
    if_neg (fun hEq' => by rw [hEq'] at h; omega), hE β (by omega), zero_add, add_zero]
  unfold subTopMonomial
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : α k = 0
  · rw [hk, Nat.cast_zero, zero_mul, map_zero, coeff_zero]
  · rw [coeff_monomial]
    refine if_neg fun hEq' => ?_
    have hlt := degSum_sub_single hk
    rw [hEq'] at hlt
    omega

theorem totalDegree_transMonomial_le (α : Fin m →₀ ℕ) :
    (transMonomial α).totalDegree ≤ degSum α := by
  refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
  rw [degSum_eq_univ_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
  have hle : (X j + C (polePart (j : ℕ)) :
      MvPolynomial (Fin m) (RatFunc ℂ)).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
    omega
  calc (α j) * (X j + C (polePart (j : ℕ)) :
      MvPolynomial (Fin m) (RatFunc ℂ)).totalDegree ≤ (α j) * 1 :=
        Nat.mul_le_mul_left _ hle
    _ = α j := Nat.mul_one _

/-- The jet substitution expanded over the support. -/
theorem jetTranslate_eq_sum (P : MvPolynomial (Fin m) (RatFunc ℂ)) :
    jetTranslate m P
      = ∑ α ∈ P.support, C (ratShift (coeff α P)) * transMonomial α := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun α _ => jetTranslate_monomial α _

theorem totalDegree_jetTranslate_le (P : MvPolynomial (Fin m) (RatFunc ℂ)) :
    (jetTranslate m P).totalDegree ≤ P.totalDegree := by
  rw [jetTranslate_eq_sum]
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  refine Finset.sup_le fun α hα => ?_
  calc (C (ratShift (coeff α P)) * transMonomial α).totalDegree
      ≤ (C (ratShift (coeff α P)) :
          MvPolynomial (Fin m) (RatFunc ℂ)).totalDegree + (transMonomial α).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + degSum α := by
        exact Nat.add_le_add (le_of_eq (MvPolynomial.totalDegree_C _))
          (totalDegree_transMonomial_le α)
    _ ≤ P.totalDegree := by
        rw [Nat.zero_add]
        exact MvPolynomial.le_totalDegree hα

/-- **Top-layer law of the jet substitution.**  On the highest jet-degree layer the
substitution acts coefficientwise by the shift. -/
theorem coeff_jetTranslate_of_le_degSum {P : MvPolynomial (Fin m) (RatFunc ℂ)}
    {β : Fin m →₀ ℕ} (hd : ∀ α ∈ P.support, degSum α ≤ degSum β) :
    coeff β (jetTranslate m P) = ratShift (coeff β P) := by
  rw [jetTranslate_eq_sum, coeff_sum]
  have hstep : ∀ α ∈ P.support,
      coeff β (C (ratShift (coeff α P)) * transMonomial α)
        = if α = β then ratShift (coeff α P) else 0 := by
    intro α hα
    rw [coeff_C_mul]
    rcases lt_or_eq_of_le (hd α hα) with hlt | heq
    · rw [coeff_transMonomial_of_degSum_lt hlt, mul_zero,
        if_neg (fun hEq => by rw [hEq] at hlt; omega)]
    · rw [coeff_transMonomial_of_degSum_eq heq.symm]
      by_cases hcase : α = β
      · rw [if_pos hcase, if_pos hcase, mul_one]
      · rw [if_neg hcase, if_neg hcase, mul_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_ite_eq' P.support β
    (fun α => ratShift (coeff α P))]
  by_cases hβ : β ∈ P.support
  · rw [if_pos hβ]
  · rw [if_neg hβ, MvPolynomial.notMem_support_iff.mp hβ, map_zero]

/-- **Subtop-layer law of the jet substitution.**  One layer below the top, the substitution
acts by the shift plus the gradient term collecting the pole parts. -/
theorem coeff_jetTranslate_of_le_degSum_succ {P : MvPolynomial (Fin m) (RatFunc ℂ)}
    {β : Fin m →₀ ℕ} (hd : ∀ α ∈ P.support, degSum α ≤ degSum β + 1) :
    coeff β (jetTranslate m P) = ratShift (coeff β P)
      + ∑ j : Fin m, ((β j + 1 : ℕ) : RatFunc ℂ) * polePart (j : ℕ)
          * ratShift (coeff (β + Finsupp.single j 1) P) := by
  rw [jetTranslate_eq_sum, coeff_sum]
  have hstep : ∀ α ∈ P.support,
      coeff β (C (ratShift (coeff α P)) * transMonomial α)
        = (if α = β then ratShift (coeff α P) else 0)
          + ∑ j : Fin m, if α = β + Finsupp.single j 1
              then ratShift (coeff α P) * ((α j : RatFunc ℂ) * polePart (j : ℕ)) else 0 := by
    intro α hα
    rw [coeff_C_mul]
    have hcases : degSum α < degSum β ∨ degSum α = degSum β
        ∨ degSum α = degSum β + 1 := by
      have := hd α hα
      omega
    rcases hcases with hlt | heq | hsucc
    · rw [coeff_transMonomial_of_degSum_lt hlt, mul_zero,
        if_neg (fun hEq => by rw [hEq] at hlt; omega)]
      rw [Finset.sum_eq_zero (fun j _ => if_neg (fun hEq => by
        rw [hEq, degSum_add, degSum_single] at hlt
        omega)), add_zero]
    · rw [coeff_transMonomial_of_degSum_eq heq.symm]
      rw [Finset.sum_eq_zero (fun j _ => if_neg (fun hEq => by
        rw [hEq, degSum_add, degSum_single] at heq
        omega)), add_zero]
      by_cases hcase : α = β
      · rw [if_pos hcase, if_pos hcase, mul_one]
      · rw [if_neg hcase, if_neg hcase, mul_zero]
    · rw [coeff_transMonomial_of_degSum_succ (by omega), Finset.mul_sum]
      rw [if_neg (fun hEq => by rw [hEq] at hsucc; omega), zero_add]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hcase : α = β + Finsupp.single j 1
      · rw [if_pos hcase, if_pos hcase]
      · rw [if_neg hcase, if_neg hcase, mul_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_ite_eq' P.support β (fun α => ratShift (coeff α P))]
    by_cases hβ : β ∈ P.support
    · rw [if_pos hβ]
    · rw [if_neg hβ, MvPolynomial.notMem_support_iff.mp hβ, map_zero]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq' P.support (β + Finsupp.single j 1)
      (fun α => ratShift (coeff α P) * ((α j : RatFunc ℂ) * polePart (j : ℕ)))]
    have happ : ((β + Finsupp.single j 1 : Fin m →₀ ℕ)) j = β j + 1 := by
      rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl]
    by_cases hβ : β + Finsupp.single j 1 ∈ P.support
    · rw [if_pos hβ, happ]
      ring
    · rw [if_neg hβ, MvPolynomial.notMem_support_iff.mp hβ, map_zero, mul_zero]

end Jet

/-! ## The elimination theorem -/

section Elimination

open MvPolynomial

/-- **No shift-stable annihilator space.**  A subset of the jet-polynomial algebra over
`ℂ(X)` closed under subtraction, `ℂ(X)`-scalar multiples, and the jet substitution, and
containing no nonzero constant, contains no nonzero element.  A double-minimal member
(minimal jet degree `D`, then minimal top-layer support) satisfies
`jetTranslate P = u·P`; the top layer is shift-periodic and hence has constant coefficient
ratios; the layer below then satisfies difference equations whose right sides lie in the
span of the pole parts, forcing the gradient of the top form to vanish — impossible in
characteristic zero once `D ≥ 1`. -/
theorem no_shift_stable_annihilator {m : ℕ}
    (I : Set (MvPolynomial (Fin m) (RatFunc ℂ)))
    (Hsub : ∀ G H, G ∈ I → H ∈ I → G - H ∈ I)
    (Hsmul : ∀ (k : RatFunc ℂ) (G), G ∈ I → C k * G ∈ I)
    (Hshift : ∀ G, G ∈ I → jetTranslate m G ∈ I)
    (Hconst : ∀ k : RatFunc ℂ, C k ∈ I → k = 0)
    (Hne : ∃ G ∈ I, G ≠ 0) : False := by
  classical
  obtain ⟨G₀, hG₀I, hG₀0⟩ := Hne
  -- minimal jet degree
  have hex : ∃ N, ∃ G, G ∈ I ∧ G ≠ 0 ∧ G.totalDegree = N :=
    ⟨G₀.totalDegree, G₀, hG₀I, hG₀0, rfl⟩
  set D := Nat.find hex with hD_def
  have hDmin : ∀ G, G ∈ I → G ≠ 0 → D ≤ G.totalDegree := fun G hGI hG0 =>
    Nat.find_min' hex ⟨G, hGI, hG0, rfl⟩
  obtain ⟨P₁, hP₁I, hP₁0, hP₁D⟩ := Nat.find_spec hex
  -- minimal top-layer support among degree-`D` members
  set topCard : MvPolynomial (Fin m) (RatFunc ℂ) → ℕ :=
    fun G => (G.support.filter fun α => degSum α = D).card with htopCard_def
  have hex2 : ∃ c, ∃ G, G ∈ I ∧ G ≠ 0 ∧ G.totalDegree = D ∧ topCard G = c :=
    ⟨topCard P₁, P₁, hP₁I, hP₁0, hP₁D, rfl⟩
  have hcmin : ∀ G, G ∈ I → G ≠ 0 → G.totalDegree = D →
      Nat.find hex2 ≤ topCard G := fun G hGI hG0 hGD =>
    Nat.find_min' hex2 ⟨G, hGI, hG0, hGD, rfl⟩
  obtain ⟨P, hPI, hP0, hPD, hPc⟩ := Nat.find_spec hex2
  -- degree at least one
  have hD1 : 1 ≤ D := by
    by_contra h
    have hD0 : D = 0 := by omega
    have hPC : P = C (coeff 0 P) :=
      (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp (hPD.trans hD0)
    have := Hconst (coeff 0 P) (hPC ▸ hPI)
    exact hP0 (by rw [hPC, this, map_zero])
  -- top exponent
  have hsupp : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP0
  obtain ⟨αs, hαs_mem, hαs_sup⟩ := Finset.exists_mem_eq_sup P.support hsupp degSum
  have hαs : degSum αs = D := by
    rw [← hPD, totalDegree_eq_sup_degSum, hαs_sup]
  set a := coeff αs P with ha_def
  have ha : a ≠ 0 := MvPolynomial.mem_support_iff.mp hαs_mem
  have hσa : ratShift a ≠ 0 := fun h0 =>
    ha (ratShift_injective (by rw [h0, map_zero]))
  -- the eliminant
  set Q := C (ratShift a) * P - C a * jetTranslate m P with hQ_def
  have hQI : Q ∈ I := Hsub _ _ (Hsmul _ _ hPI) (Hsmul _ _ (Hshift _ hPI))
  have hdegall : ∀ α ∈ P.support, degSum α ≤ D := fun α hα => by
    rw [← hPD]
    exact MvPolynomial.le_totalDegree hα
  have hQtop : ∀ β, degSum β = D →
      coeff β Q = ratShift a * coeff β P - a * ratShift (coeff β P) := by
    intro β hβ
    rw [hQ_def, coeff_sub, coeff_C_mul, coeff_C_mul,
      coeff_jetTranslate_of_le_degSum (fun α hα => by rw [hβ]; exact hdegall α hα)]
  -- the eliminant vanishes
  have hQ0 : Q = 0 := by
    by_contra hQne
    have hQD : Q.totalDegree = D := by
      refine le_antisymm ?_ (hDmin Q hQI hQne)
      rw [hQ_def]
      refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
      refine max_le ?_ ?_
      · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        rw [MvPolynomial.totalDegree_C, Nat.zero_add, hPD]
      · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        rw [MvPolynomial.totalDegree_C, Nat.zero_add]
        rw [← hPD]
        exact totalDegree_jetTranslate_le P
    have hss : (Q.support.filter fun α => degSum α = D)
        ⊂ (P.support.filter fun α => degSum α = D) := by
      rw [Finset.ssubset_iff_of_subset ?_]
      · refine ⟨αs, Finset.mem_filter.mpr ⟨hαs_mem, hαs⟩, ?_⟩
        intro hmem
        have hcoeffQ : coeff αs Q = 0 := by
          rw [hQtop αs hαs, ← ha_def]
          ring
        exact (MvPolynomial.mem_support_iff.mp (Finset.mem_filter.mp hmem).1) hcoeffQ
      · intro β hβ
        obtain ⟨hβQ, hβD⟩ := Finset.mem_filter.mp hβ
        refine Finset.mem_filter.mpr ⟨?_, hβD⟩
        rw [MvPolynomial.mem_support_iff]
        intro hPβ
        apply MvPolynomial.mem_support_iff.mp hβQ
        rw [hQtop β hβD, hPβ, map_zero, mul_zero, mul_zero, sub_zero]
    have hlt : topCard Q < topCard P := Finset.card_lt_card hss
    have hle := hcmin Q hQI hQne hQD
    omega
  -- top layer: constant coefficient ratios
  have htop : ∀ β, degSum β = D →
      ∃ t : ℂ, coeff β P = algebraMap ℂ (RatFunc ℂ) t * a := by
    intro β hβ
    have h0 : ratShift a * coeff β P - a * ratShift (coeff β P) = 0 := by
      rw [← hQtop β hβ, hQ0, coeff_zero]
    have hfix : ratShift (coeff β P / a) = coeff β P / a := by
      rw [map_div₀, div_eq_div_iff hσa ha]
      linear_combination -h0
    obtain ⟨t, ht⟩ := ratShift_fixed_eq_const hfix
    refine ⟨t, ?_⟩
    rw [← ht]
    field_simp
  -- subtop layer: the gradient of the top form vanishes
  have hkill : ∀ β, degSum β + 1 = D → ∀ j : Fin m,
      coeff (β + Finsupp.single j 1) P = 0 := by
    intro β hβ j
    choose t ht using fun (k : Fin m) =>
      htop (β + Finsupp.single k 1) (by rw [degSum_add, degSum_single]; omega)
    have hcoeffQ : coeff β Q = 0 := by rw [hQ0, coeff_zero]
    rw [hQ_def, coeff_sub, coeff_C_mul, coeff_C_mul,
      coeff_jetTranslate_of_le_degSum_succ
        (fun α hα => by
          have := hdegall α hα
          omega)] at hcoeffQ
    -- rewrite the shifted top coefficients through the constants
    have hsum : ∑ k : Fin m, ((β k + 1 : ℕ) : RatFunc ℂ) * polePart (k : ℕ)
          * ratShift (coeff (β + Finsupp.single k 1) P)
        = ratShift a * ∑ k : Fin m, ((β k + 1 : ℕ) : RatFunc ℂ)
            * algebraMap ℂ (RatFunc ℂ) (t k) * polePart (k : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ht k, map_mul, ratShift_const]
      ring
    rw [hsum] at hcoeffQ
    set S := ∑ k : Fin m, ((β k + 1 : ℕ) : RatFunc ℂ)
      * algebraMap ℂ (RatFunc ℂ) (t k) * polePart (k : ℕ) with hS_def
    -- the difference equation for the coefficient ratio
    have hw : ratShift (coeff β P / a) - coeff β P / a
        = ∑ k : Fin m, algebraMap ℂ (RatFunc ℂ) (-(((β k : ℂ) + 1) * t k))
            * polePart (k : ℕ) := by
      have hnum : ratShift (coeff β P) * a - ratShift a * coeff β P
          = (a * ratShift a) * (-S) := by
        linear_combination -hcoeffQ
      rw [map_div₀, div_sub_div _ _ hσa ha, hnum,
        show ratShift a * a = a * ratShift a by ring,
        mul_div_cancel_left₀ _ (mul_ne_zero ha hσa)]
      rw [hS_def, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_neg, map_mul]
      rw [show ((β k : ℂ) + 1) = (((β k + 1 : ℕ) : ℂ)) by push_cast; ring,
        map_natCast]
      ring
    have hδ := ratShift_sub_polePart_combination hw j
    have ht0 : t j = 0 := by
      have hne : ((β j : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero (β j)
      have := neg_eq_zero.mp hδ
      exact (mul_eq_zero.mp this).resolve_left hne
    rw [ht j, ht0, map_zero, zero_mul]
  -- contradiction at the top exponent
  obtain ⟨j, hj⟩ := exists_apply_ne_zero_of_degSum_pos (by omega : 0 < degSum αs)
  have hres : αs - Finsupp.single j 1 + Finsupp.single j 1 = αs :=
    sub_single_add_single hj
  have hβdeg : degSum (αs - Finsupp.single j 1) + 1 = D := by
    rw [← hαs]
    exact degSum_sub_single hj
  have := hkill (αs - Finsupp.single j 1) hβdeg j
  rw [hres] at this
  exact ha this

end Elimination

end GaloisForLFunctions
