import GaloisForLFunctions.RHTower.HyperellipticRiemannHypothesis
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheEffectivityCalculus
import GaloisForLFunctions.ArithmeticEffectivityTheory.NaiveHeightsAreTraces

/-!
# The hyperelliptic calibration

For an odd prime `p` and `f ∈ 𝔽_p[X]` squarefree, split, of odd degree `m = 2g + 1`, the reciprocal
roots `ω_i` of the L-function of `y² = f(x)` give a curve datum of genus `g`
(`hyperellipticDatum`): `q = p`, `β_i = ω_i/√p`. The conjugation symmetry holds because the
L-polynomial has integer coefficients (`map_conj_lRoots`); the functional equation `β ↦ β⁻¹` is
conjugation, since the datum is unitary (`hyperellipticDatum_unitary`, by Stepanov's count and the
Gauss-sum modulus). Its Lefschetz numbers are the point counts of the smooth projective model —
the affine points plus the one point at infinity (`hyperellipticDatum_pointCount`).

Hence AET's effectivity laws hold on actual curves of every genus, unconditionally: every
Frobenius window carries an effectivity function bounded on degree levels
(`hyperellipticDatum_window_exists_effectivity`) and the integral Rosati form on `ℤ[F]` has a naive
height (`hyperellipticDatum_exists_naiveHeight`). The sign is carried by two cardinalities:
Stepanov's auxiliary-section count and `|τ|² = p`.
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

variable {p : ℕ} [hp : Fact p.Prime]

/-- The reciprocal roots of a split odd-degree hyperelliptic curve have modulus `√p`. -/
theorem norm_rootEnum_eq (hp2 : p ≠ 2) {f : (ZMod p)[X]} (hsq : Squarefree f) (hsplit : f.Splits)
    (hodd : Odd f.natDegree) (i : Fin (lRoots f).toList.length) :
    ‖rootEnum (lRoots f) i‖ = Real.sqrt p :=
  (riemannHypothesis_splitHyperelliptic.{0} hp2 hsq hsplit hodd).2.1 _ (rootEnum_mem _ i)

theorem sqrt_prime_ne_zero : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos)).ne'

/-- **The curve datum of `y² = f(x)`**: `q = p`, `β_i = ω_i/√p`, conjugation and the functional
equation both realized by the conjugation permutation of the reciprocal roots. -/
noncomputable def hyperellipticDatum (hp2 : p ≠ 2) {f : (ZMod p)[X]} (hsq : Squarefree f)
    (hsplit : f.Splits) (hodd : Odd f.natDegree) : CurveDatum (Fin (lRoots f).toList.length) where
  q := p
  one_lt_q := by exact_mod_cast hp.out.one_lt
  β i := rootEnum (lRoots f) i / (Real.sqrt p : ℂ)
  conjPerm := (exists_conjPerm f).choose
  β_conjPerm i := by
    rw [(exists_conjPerm f).choose_spec i, map_div₀, Complex.conj_ofReal]
  fePerm := (exists_conjPerm f).choose
  β_fePerm i := by
    rw [(exists_conjPerm f).choose_spec i, div_mul_div_comm, Complex.conj_mul',
      norm_rootEnum_eq hp2 hsq hsplit hodd i, ← Complex.ofReal_mul, ← sq, Complex.ofReal_pow,
      div_self (pow_ne_zero 2 sqrt_prime_ne_zero)]

/-- The genus: `2g = m − 1` normalized eigenvalues. -/
theorem card_hyperellipticDatum {f : (ZMod p)[X]} (hodd : Odd f.natDegree) :
    Fintype.card (Fin (lRoots f).toList.length) = f.natDegree - 1 := by
  rw [Fintype.card_fin, Multiset.length_toList, card_lRoots f hodd.pos]

variable (hp2 : p ≠ 2) {f : (ZMod p)[X]} (hsq : Squarefree f) (hsplit : f.Splits)
  (hodd : Odd f.natDegree)

/-- **Unitarity**, by counting. -/
theorem hyperellipticDatum_unitary : ∀ i, ‖(hyperellipticDatum hp2 hsq hsplit hodd).β i‖ = 1 := by
  intro i
  change ‖rootEnum (lRoots f) i / (Real.sqrt p : ℂ)‖ = 1
  rw [norm_div, norm_rootEnum_eq hp2 hsq hsplit hodd i, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr
      (by exact_mod_cast hp.out.pos)).ne']

/-- **The Lefschetz numbers are point counts**: over the extension `E` of degree `n`,
`N_n = #{(x, y) ∈ E² : y² = f(x)} + 1`, the affine points plus the point at infinity. -/
theorem hyperellipticDatum_pointCount (E : Type*) [Field E] [Fintype E] [Algebra (ZMod p) E] :
    (hyperellipticDatum hp2 hsq hsplit hodd).pointCount (Module.finrank (ZMod p) E) =
      (univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card + 1 := by
  have hsum := (riemannHypothesis_splitHyperelliptic hp2 hsq hsplit hodd).2.2 E
  set D := hyperellipticDatum hp2 hsq hsplit hodd
  set n := Module.finrank (ZMod p) E
  have hE : ringChar E ≠ 2 := by
    rw [← Algebra.ringChar_eq (ZMod p) E, ZMod.ringChar_zmod_n]; exact hp2
  have hcardE : (Fintype.card E : ℝ) = (p : ℝ) ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]; push_cast; rfl
  have hcount := card_points_eq hE (f.map (algebraMap (ZMod p) E))
  simp only [eval_map, ← aeval_def] at hcount
  -- the trace times `√q^n` is the power sum of the `ω_i`
  have hs : (D.sqrtq : ℂ) ^ n * D.powerSum n = ((lRoots f).map (· ^ n)).sum := by
    change ((Real.sqrt p : ℝ) : ℂ) ^ n * ∑ i, (rootEnum (lRoots f) i / (Real.sqrt p : ℂ)) ^ n = _
    rw [Finset.mul_sum, Finset.sum_eq_multiset_sum]
    conv_rhs => rw [← univ_map_rootEnum (lRoots f), Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun i _ => ?_
    rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero n sqrt_prime_ne_zero)]
    rfl
  have hext : ((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℂ) = extHyp (E := E) f := by
    unfold extHyp; push_cast; rfl
  have hC : ((D.sqrtq ^ n * D.trace n : ℝ) : ℂ) =
      -((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℂ) := by
    rw [hext, hsum, neg_neg, Complex.ofReal_mul, Complex.ofReal_pow, ← D.powerSum_eq_trace, hs]
  have hR : D.sqrtq ^ n * D.trace n = -((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℝ) := by
    exact_mod_cast hC
  have hq : D.q = p := rfl
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
      RiemannInequality ((hyperellipticDatum hp2 hsq hsplit hodd).windowSurface W)
        (a • ((hyperellipticDatum hp2 hsq hsplit hodd).windowSurface W).H +
          b • ((hyperellipticDatum hp2 hsq hsplit hodd).windowSurface W).V) χ₀ h ∧
        DegreeBounded ((hyperellipticDatum hp2 hsq hsplit hodd).windowSurface W) h :=
  ((CurveDatum.unitary_iff_forall_window_exists_effectivity _ a b χ₀).mp
    (hyperellipticDatum_unitary hp2 hsq hsplit hodd)) W

/-- **Naive heights on actual curves**: the integral Rosati form of `y² = f(x)` on `ℤ[F]` is at
bounded distance from a function bounded below. -/
theorem hyperellipticDatum_exists_naiveHeight :
    ∃ h : ℤ[X] → ℝ, ∃ K B : ℝ, (∀ P, -K ≤ h P) ∧
      ∀ P, |h P - intRosatiDeg (hyperellipticDatum hp2 hsq hsplit hodd) P| ≤ B :=
  (exists_naiveHeight_iff_unitary _).mpr (hyperellipticDatum_unitary hp2 hsq hsplit hodd)

end GaloisForLFunctions.ArithmeticEffectivityTheory
