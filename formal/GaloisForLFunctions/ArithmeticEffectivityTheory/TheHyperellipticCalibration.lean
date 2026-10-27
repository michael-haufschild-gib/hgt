import GaloisForLFunctions.RHTower.HyperellipticDescent
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheEffectivityCalculus
import GaloisForLFunctions.ArithmeticEffectivityTheory.NaiveHeightsAreTraces

/-!
# The hyperelliptic calibration

For `F` finite of odd characteristic, `q = |F|`, and `f ∈ F[X]` squarefree of odd degree
`m = 2g + 1`, the reciprocal roots `ω_i` of the L-function of `y² = f(x)` give a curve datum of
genus `g` (`hyperellipticDatum`): `β_i = ω_i/√q`. The conjugation symmetry holds because the
L-polynomial has integer coefficients (`map_conj_lRoots`); the functional equation `β ↦ β⁻¹` is
conjugation, since the datum is unitary (`hyperellipticDatum_unitary`, by Stepanov's count, the
Gauss-sum modulus and descent from the splitting field). Its Lefschetz numbers are the point
counts of the smooth projective model — the affine points plus the one point at infinity
(`hyperellipticDatum_pointCount`).

Hence AET's effectivity laws hold on actual curves of every genus over every finite field of odd
characteristic, unconditionally: every Frobenius window carries an effectivity function bounded on
degree levels (`hyperellipticDatum_window_exists_effectivity`) and the integral Rosati form on
`ℤ[F]` has a naive height (`hyperellipticDatum_exists_naiveHeight`). The sign is carried by two
cardinalities: Stepanov's auxiliary-section count and `|τ|² = q`.
-/

open Polynomial Finset

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

open ArithmeticCastelnuovoSeveri RHTower.Hyperelliptic RHTower.WeilKloosterman

attribute [local instance] Classical.propDecidable

/-- Two families with the same multiset of values differ by a permutation of the index. -/
theorem exists_perm_of_map_univ_eq {ι β : Type*} [Fintype ι] (f g : ι → β)
    (h : univ.val.map f = univ.val.map g) : ∃ σ : Equiv.Perm ι, ∀ i, g (σ i) = f i := by
  have hc : ∀ c, Fintype.card {i // f i = c} = Fintype.card {i // g i = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card, Finset.filter_val, eq_comm] using this
  exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hc c),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

section Roots

variable {F : Type*} [Field F] [Fintype F]

/-- The degree sums are integers, hence fixed by complex conjugation. -/
theorem conj_degSum (f : F[X]) (k : ℕ) :
    starRingEnd ℂ (RHTower.Hyperelliptic.degSum f k) = RHTower.Hyperelliptic.degSum f k := by
  unfold RHTower.Hyperelliptic.degSum degSumW
  rw [map_sum]
  refine sum_congr rfl fun h _ => ?_
  simp [hypW]

/-- **The reciprocal roots are closed under conjugation**: the L-polynomial is real. -/
theorem map_conj_lRoots (f : F[X]) : (lRoots f).map (starRingEnd ℂ) = lRoots f := by
  have hreal : (lPoly f).map (starRingEnd ℂ) = lPoly f := by
    unfold lPoly
    rw [Polynomial.map_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, conj_degSum]
  rw [lRoots, roots_map_of_injective_of_card_eq_natDegree (starRingEnd ℂ).injective
    (IsAlgClosed.card_roots_eq_natDegree (k := ℂ)), hreal]

theorem rootEnum_mem (s : Multiset ℂ) (i : Fin s.toList.length) : rootEnum s i ∈ s :=
  Multiset.mem_toList.mp (List.get_mem _ _)

/-- A permutation of the reciprocal roots realizing complex conjugation. -/
theorem exists_conjPerm (f : F[X]) : ∃ σ : Equiv.Perm (Fin (lRoots f).toList.length),
    ∀ i, rootEnum (lRoots f) (σ i) = starRingEnd ℂ (rootEnum (lRoots f) i) := by
  refine exists_perm_of_map_univ_eq _ _ ?_
  rw [univ_map_rootEnum, show (univ.val.map fun i => starRingEnd ℂ (rootEnum (lRoots f) i)) =
    (univ.val.map (rootEnum (lRoots f))).map (starRingEnd ℂ) by rw [Multiset.map_map]; rfl,
    univ_map_rootEnum, map_conj_lRoots]

end Roots

section Datum

variable {F : Type*} [Field F] [Fintype F]

/-- The reciprocal roots of an odd-degree hyperelliptic curve have modulus `√q`. -/
theorem norm_rootEnum_eq (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hodd : Odd f.natDegree) (i : Fin (lRoots f).toList.length) :
    ‖rootEnum (lRoots f) i‖ = Real.sqrt (Fintype.card F) :=
  (riemannHypothesis_oddHyperelliptic.{_, 0} hF hsq hodd).2.1 _ (rootEnum_mem _ i)

omit [Field F] in
theorem sqrt_card_ne_zero [Nonempty F] : ((Real.sqrt (Fintype.card F) : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)).ne'

/-- **The curve datum of `y² = f(x)`**: `q = |F|`, `β_i = ω_i/√q`, conjugation and the functional
equation both realized by the conjugation permutation of the reciprocal roots. -/
noncomputable def hyperellipticDatum (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hodd : Odd f.natDegree) : CurveDatum (Fin (lRoots f).toList.length) where
  q := Fintype.card F
  one_lt_q := by exact_mod_cast Fintype.one_lt_card
  β i := rootEnum (lRoots f) i / (Real.sqrt (Fintype.card F) : ℂ)
  conjPerm := (exists_conjPerm f).choose
  β_conjPerm i := by
    rw [(exists_conjPerm f).choose_spec i, map_div₀, Complex.conj_ofReal]
  fePerm := (exists_conjPerm f).choose
  β_fePerm i := by
    rw [(exists_conjPerm f).choose_spec i, div_mul_div_comm, Complex.conj_mul',
      norm_rootEnum_eq hF hsq hodd i, ← Complex.ofReal_mul, ← sq, Complex.ofReal_pow,
      div_self (pow_ne_zero 2 sqrt_card_ne_zero)]

omit [Fintype F] in
/-- The genus: `2g = m − 1` normalized eigenvalues. -/
theorem card_hyperellipticDatum [Fintype F] {f : F[X]} (hodd : Odd f.natDegree) :
    Fintype.card (Fin (lRoots f).toList.length) = f.natDegree - 1 := by
  rw [Fintype.card_fin, Multiset.length_toList, card_lRoots f hodd.pos]

variable (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f) (hodd : Odd f.natDegree)

/-- **Unitarity**, by counting. -/
theorem hyperellipticDatum_unitary : ∀ i, ‖(hyperellipticDatum hF hsq hodd).β i‖ = 1 := by
  intro i
  change ‖rootEnum (lRoots f) i / (Real.sqrt (Fintype.card F) : ℂ)‖ = 1
  rw [norm_div, norm_rootEnum_eq hF hsq hodd i, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr
      (by exact_mod_cast Fintype.card_pos)).ne']

/-- **The Lefschetz numbers are point counts**: over the extension `E` of degree `n`,
`N_n = #{(x, y) ∈ E² : y² = f(x)} + 1`, the affine points plus the point at infinity. -/
theorem hyperellipticDatum_pointCount (E : Type*) [Field E] [Fintype E] [Algebra F E] :
    (hyperellipticDatum hF hsq hodd).pointCount (Module.finrank F E) =
      (univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card + 1 := by
  have hsum := (riemannHypothesis_oddHyperelliptic hF hsq hodd).2.2 E
  set D := hyperellipticDatum hF hsq hodd
  set n := Module.finrank F E
  have hE : ringChar E ≠ 2 := by rwa [← Algebra.ringChar_eq F E]
  have hcardE : (Fintype.card E : ℝ) = (Fintype.card F : ℝ) ^ n := by
    rw [Module.card_eq_pow_finrank (K := F)]; push_cast; rfl
  have hcount := card_points_eq hE (f.map (algebraMap F E))
  simp only [eval_map, ← aeval_def] at hcount
  -- the trace times `√q^n` is the power sum of the `ω_i`
  have hs : (D.sqrtq : ℂ) ^ n * D.powerSum n = ((lRoots f).map (· ^ n)).sum := by
    change ((Real.sqrt (Fintype.card F) : ℝ) : ℂ) ^ n *
      ∑ i, (rootEnum (lRoots f) i / (Real.sqrt (Fintype.card F) : ℂ)) ^ n = _
    rw [Finset.mul_sum, Finset.sum_eq_multiset_sum]
    conv_rhs => rw [← univ_map_rootEnum (lRoots f), Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun i _ => ?_
    rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero n sqrt_card_ne_zero)]
    rfl
  have hext : ((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℂ) = extHyp (E := E) f := by
    unfold extHyp; push_cast; rfl
  have hC : ((D.sqrtq ^ n * D.trace n : ℝ) : ℂ) =
      -((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℂ) := by
    rw [hext, hsum, neg_neg, Complex.ofReal_mul, Complex.ofReal_pow, ← D.powerSum_eq_trace, hs]
  have hR : D.sqrtq ^ n * D.trace n = -((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℝ) := by
    exact_mod_cast hC
  have hq : D.q = Fintype.card F := rfl
  unfold CurveDatum.pointCount
  rw [hR, hq, ← hcardE]
  have := congrArg (fun z : ℤ => (z : ℝ)) hcount
  push_cast at this ⊢
  linarith

/-- **Effectivity on actual curves**: every Frobenius window of `y² = f(x)` carries an effectivity
function, with the Riemann inequality for any ample-type class and constant, bounded on degree
levels. -/
theorem hyperellipticDatum_window_exists_effectivity (a b χ₀ : ℝ) (W : Finset ℕ) :
    ∃ h : SpanCycle → ℝ,
      RiemannInequality ((hyperellipticDatum hF hsq hodd).windowSurface W)
        (a • ((hyperellipticDatum hF hsq hodd).windowSurface W).H +
          b • ((hyperellipticDatum hF hsq hodd).windowSurface W).V) χ₀ h ∧
        DegreeBounded ((hyperellipticDatum hF hsq hodd).windowSurface W) h :=
  ((CurveDatum.unitary_iff_forall_window_exists_effectivity _ a b χ₀).mp
    (hyperellipticDatum_unitary hF hsq hodd)) W

/-- **Naive heights on actual curves**: the integral Rosati form of `y² = f(x)` on `ℤ[F]` is at
bounded distance from a function bounded below. -/
theorem hyperellipticDatum_exists_naiveHeight :
    ∃ h : ℤ[X] → ℝ, ∃ K B : ℝ, (∀ P, -K ≤ h P) ∧
      ∀ P, |h P - intRosatiDeg (hyperellipticDatum hF hsq hodd) P| ≤ B :=
  (exists_naiveHeight_iff_unitary _).mpr (hyperellipticDatum_unitary hF hsq hodd)

end Datum

end GaloisForLFunctions.ArithmeticEffectivityTheory
