import GaloisForLFunctions.OrderSixMetaplecticTheory.ComplexConjugationActsOnTheCubicSymbols
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.RationalSourceProjection
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicScatteringContinuation

/-!
# The Gauss-sum Dirichlet series are conjugation symmetric

The Fourier coefficients of the cubic Eisenstein series at the two cusps of `Γ(3)` are Dirichlet series
in cubic Gauss sums:

* at `∞`: `D(s, h) = Σ_{3 | c} N(c)^{−s} Σ_{d mod 3c} (c/d)₃ e(ξ_h d / c)` (`arithmeticDirichletSeries`);
* at `0`: `U(s, h) = Σ_{I good} N(I)^{−s} g(h, c_I)` (`unramifiedCubicGaussSeries`).

Conjugating the denominator `c ↦ c̄` and the residue `d ↦ d̄` conjugates every term, because the cubic
symbol conjugates (`symbol_conjO`) and the different `1 + 2ω` is purely imaginary. Hence
`D(s̄, h̄) = \overline{D(s, h)}` and `U(s̄, h̄) = \overline{U(s, h)}` for every `s`
(`arithmeticDirichletSeries_conj`, `unramifiedCubicGaussSeries_conj`).

The Whittaker factor `W(s, h) = ∫₅⁶ v^{−s−1} K_s(ξ_h v) dv` satisfies `W(s̄, h̄) = \overline{W(s, h)}`
(`cuspWhittakerHeightFactor_conj`): `ξ_{h̄} = −\overline{ξ_h}` because the different is purely imaginary, and
the hyperbolic kernel `(1 + |z|²)^{−s}` is real and invariant under `z ↦ z̄`.
-/

noncomputable section

open MeasureTheory

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein

/-! ### Real powers -/

theorem ofReal_cpow_star {r : ℝ} (hr : 0 ≤ r) (w : ℂ) : (r : ℂ) ^ (star w) = star ((r : ℂ) ^ w) := by
  rw [Complex.star_def, Complex.cpow_conj _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hr]; exact Real.pi_ne_zero.symm), Complex.conj_ofReal]

theorem natCast_cpow_star (n : ℕ) (w : ℂ) : (n : ℂ) ^ (star w) = star ((n : ℂ) ^ w) := by
  have h := ofReal_cpow_star (Nat.cast_nonneg (α := ℝ) n) w
  simpa only [Complex.ofReal_natCast] using h

/-! ### Conjugate frequencies -/

theorem star_cuspFrequency (h : O) : star (cuspFrequency h) = -cuspFrequency (conjO h) := by
  unfold cuspFrequency
  rw [star_div₀, star_mul', star_ringComplex_traceLambda, ringComplex_conjO, star_ofNat]
  ring

theorem tracePhase_frequency_conj (h c d : O) :
    tracePhase (cuspFrequency (conjO h) * ringComplex (conjO d) / ringComplex (conjO c)) =
      star (tracePhase (cuspFrequency h * ringComplex d / ringComplex c)) := by
  rw [← tracePhase_neg_star, star_div₀, star_mul', star_cuspFrequency, ← ringComplex_conjO,
    ← ringComplex_conjO]
  ring_nf

/-! ### The Whittaker factor -/

theorem hyperbolicKernel_star (s z : ℂ) : hyperbolicKernel (star s) z = star (hyperbolicKernel s z) := by
  unfold hyperbolicKernel
  rw [show -star s = star (-s) from (star_neg s).symm, ofReal_cpow_star (by positivity)]

theorem hyperbolicKernel_star_arg (s z : ℂ) : hyperbolicKernel s (star z) = hyperbolicKernel s z := by
  unfold hyperbolicKernel
  rw [norm_star]

/-- **The source kernel under conjugation:** `K_{s̄}(−ξ̄) = \overline{K_s(ξ)}`, by `z ↦ z̄` in the integral. -/
theorem sourceFourierKernel_conj (s ξ : ℂ) :
    sourceFourierKernel (star s) (-star ξ) = star (sourceFourierKernel s ξ) := by
  have hmp : MeasurePreserving (starRingEnd ℂ) volume volume := Complex.conjLIE.measurePreserving
  have hemb : MeasurableEmbedding (starRingEnd ℂ) := Complex.conjLIE.toHomeomorph.measurableEmbedding
  have hpt : ∀ z : ℂ, hyperbolicKernel (star s) ((starRingEnd ℂ) z) * tracePhase (-(-star ξ) * (starRingEnd ℂ) z) =
      (starRingEnd ℂ) (hyperbolicKernel s z * tracePhase (-ξ * z)) := by
    intro z
    have h1 : hyperbolicKernel (star s) ((starRingEnd ℂ) z) = star (hyperbolicKernel s z) := by
      rw [show (starRingEnd ℂ) z = star z from rfl, hyperbolicKernel_star_arg, hyperbolicKernel_star]
    have h2 : tracePhase (-(-star ξ) * (starRingEnd ℂ) z) = star (tracePhase (-ξ * z)) := by
      rw [← tracePhase_neg_star]
      congr 1
      rw [star_mul', star_neg, neg_neg, neg_mul, neg_neg]
      rfl
    rw [h1, h2, ← star_mul']
    rfl
  unfold sourceFourierKernel
  calc ∫ z, hyperbolicKernel (star s) z * tracePhase (-(-star ξ) * z)
      = ∫ z, hyperbolicKernel (star s) ((starRingEnd ℂ) z) * tracePhase (-(-star ξ) * (starRingEnd ℂ) z) :=
        (hmp.integral_comp hemb (fun z => hyperbolicKernel (star s) z * tracePhase (-(-star ξ) * z))).symm
    _ = ∫ z, (starRingEnd ℂ) (hyperbolicKernel s z * tracePhase (-ξ * z)) := by
        congr 1
        funext z
        exact hpt z
    _ = star (∫ z, hyperbolicKernel s z * tracePhase (-ξ * z)) := integral_conj

/-- **The Whittaker factor under conjugation:** `W(s̄, h̄) = \overline{W(s, h)}`. -/
theorem cuspWhittakerHeightFactor_conj (h : O) (s : ℂ) :
    cuspWhittakerHeightFactor (star s) (conjO h) = star (cuspWhittakerHeightFactor s h) := by
  unfold cuspWhittakerHeightFactor
  calc ∫ v in Set.Icc (5 : ℝ) 6, (v : ℂ) ^ (-star s - 1) * sourceFourierKernel (star s) (cuspFrequency (conjO h) * v)
      = ∫ v in Set.Icc (5 : ℝ) 6,
          (starRingEnd ℂ) ((v : ℂ) ^ (-s - 1) * sourceFourierKernel s (cuspFrequency h * v)) := by
        refine setIntegral_congr_fun measurableSet_Icc fun v hv => ?_
        have hv0 : (0 : ℝ) ≤ v := by linarith [hv.1]
        have hξ : cuspFrequency (conjO h) * v = -star (cuspFrequency h * v) := by
          rw [star_mul', star_cuspFrequency, show star (v : ℂ) = v from Complex.conj_ofReal v]
          ring
        change _ = star (_ * _)
        rw [star_mul', ← sourceFourierKernel_conj, ← hξ, ← ofReal_cpow_star hv0, star_sub, star_neg, star_one]
    _ = star (∫ v in Set.Icc (5 : ℝ) 6, (v : ℂ) ^ (-s - 1) * sourceFourierKernel s (cuspFrequency h * v)) :=
        integral_conj

/-! ### The Dirichlet series at the cusp `∞` -/

theorem conjO_ofNat (n : ℕ) [n.AtLeastTwo] : conjO (OfNat.ofNat n : O) = OfNat.ofNat n := map_ofNat conjO n

theorem three_dvd_conjO {x : O} (hx : (3 : O) ∣ x) : (3 : O) ∣ conjO x := by
  obtain ⟨k, rfl⟩ := hx
  exact ⟨conjO k, by rw [map_mul, conjO_ofNat]⟩

theorem three_dvd_conjO_iff {x : O} : (3 : O) ∣ conjO x ↔ (3 : O) ∣ x :=
  ⟨fun h => by simpa only [conjO_conjO] using three_dvd_conjO h, three_dvd_conjO⟩

theorem three_dvd_conjO_sub_one {d : O} : (3 : O) ∣ conjO d - 1 ↔ (3 : O) ∣ d - 1 := by
  rw [show conjO d - 1 = conjO (d - 1) by rw [map_sub, map_one], three_dvd_conjO_iff]

theorem denominatorCondition_conjO {c d : O} :
    denominatorCondition (conjO c) (conjO d) ↔ denominatorCondition c d := by
  unfold denominatorCondition
  rw [three_dvd_conjO_sub_one]
  refine and_congr_left' ⟨fun h => ?_, fun h => h.map (conjO : O →+* O)⟩
  simpa only [RingHom.coe_coe, conjO_conjO] using h.map (conjO : O →+* O)

/-- Residues modulo `3c` and modulo `3c̄`. -/
def conjDenominatorResidue (c : O) : DenominatorResidue c ≃+* DenominatorResidue (conjO c) :=
  Ideal.quotientEquiv _ _ conjO (by rw [Ideal.map_span, Set.image_singleton, map_mul, map_ofNat]; rfl)

theorem conjDenominatorResidue_mk (c x : O) :
    conjDenominatorResidue c (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (conjO x) :=
  Ideal.quotientEquiv_mk _ _ _ _ x

theorem denominatorRep_conj (c : O) (r : DenominatorResidue c) :
    ∃ n : O, denominatorRep (conjO c) (conjDenominatorResidue c r) =
      conjO (denominatorRep c r) + 3 * conjO c * n := by
  have h : Ideal.Quotient.mk (Ideal.span {3 * conjO c}) (denominatorRep (conjO c) (conjDenominatorResidue c r)) =
      Ideal.Quotient.mk _ (conjO (denominatorRep c r)) := by
    rw [denominatorRep_spec, ← conjDenominatorResidue_mk, denominatorRep_spec]
  obtain ⟨n, hn⟩ := Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h)
  exact ⟨n, by linear_combination hn⟩

/-- Conjugation of admissible residues. -/
def conjAdmissibleResidue (c : O) : AdmissibleResidue c ≃ AdmissibleResidue (conjO c) :=
  (conjDenominatorResidue c).toEquiv.subtypeEquiv fun r => by
    obtain ⟨n, hn⟩ := denominatorRep_conj c r
    change _ ↔ denominatorCondition (conjO c) (denominatorRep (conjO c) (conjDenominatorResidue c r))
    rw [hn, denominatorCondition_shift, denominatorCondition_conjO]

/-- **The residue sum conjugates.** `S(h̄, c̄) = \overline{S(h, c)}` for `3 ∣ c`. -/
theorem arithmeticResidueSum_conj (h c : O) (hc : c ≠ 0) (hc3 : (3 : O) ∣ c) :
    arithmeticResidueSum (conjO h) (conjO c) = star (arithmeticResidueSum h c) := by
  unfold arithmeticResidueSum
  rw [tsum_star, ← (conjAdmissibleResidue c).tsum_eq]
  congr 1
  funext r
  obtain ⟨n, hn⟩ := denominatorRep_conj c r.1
  have hd : (3 : O) ∣ denominatorRep c r.1 - 1 := r.2.2
  change ringComplex (symbol (conjO c) (denominatorRep (conjO c) (conjDenominatorResidue c r.1))) *
      tracePhase (cuspFrequency (conjO h) * ringComplex (denominatorRep (conjO c) (conjDenominatorResidue c r.1)) /
        ringComplex (conjO c)) = _
  have hc' : ringComplex (conjO c) ≠ 0 := ringComplex_ne_zero (conjO_ne_zero hc)
  have hsplit : cuspFrequency (conjO h) * ringComplex (conjO (denominatorRep c r.1) + 3 * conjO c * n) /
      ringComplex (conjO c) = cuspFrequency (conjO h) * ringComplex (conjO (denominatorRep c r.1)) /
        ringComplex (conjO c) + cuspFrequency (conjO h) * (3 * ringComplex n) := by
    rw [map_add, map_mul, map_mul, map_ofNat]
    field_simp
  rw [hn, row_symbol_shift _ _ _ (three_dvd_conjO hc3) (three_dvd_conjO_sub_one.mpr hd), hsplit,
    AddChar.map_add_eq_mul, cuspFrequency_period, mul_one, ringComplex_symbol_conjO,
    tracePhase_frequency_conj, star_mul']

/-- Conjugation of lower-left entries divisible by `3`. -/
def conjLevelLower : LevelLower ≃ LevelLower where
  toFun c := ⟨conjO c.1, three_dvd_conjO c.2⟩
  invFun c := ⟨conjO c.1, three_dvd_conjO c.2⟩
  left_inv c := Subtype.ext (conjO_conjO c.1)
  right_inv c := Subtype.ext (conjO_conjO c.1)

theorem arithmeticDirichletTerm_conj (s : ℂ) (h : O) (c : LevelLower) :
    arithmeticDirichletTerm (star s) (conjO h) (conjLevelLower c) = star (arithmeticDirichletTerm s h c) := by
  unfold arithmeticDirichletTerm
  rw [show (conjLevelLower c).1 = conjO c.1 from rfl]
  by_cases hc : c.1 = 0
  · rw [if_pos (show conjO c.1 = 0 by rw [hc, map_zero]), if_pos hc, star_zero]
  · rw [if_neg (conjO_ne_zero hc), if_neg hc, ringComplex_conjO, norm_star,
      show -star s = star (-s) from (star_neg s).symm, ofReal_cpow_star (by positivity),
      arithmeticResidueSum_conj h c.1 hc c.2, star_mul']

/-- **The Dirichlet series at `∞` is conjugation symmetric.** -/
theorem arithmeticDirichletSeries_conj (s : ℂ) (h : O) :
    arithmeticDirichletSeries (star s) (conjO h) = star (arithmeticDirichletSeries s h) := by
  unfold arithmeticDirichletSeries
  rw [tsum_star, ← conjLevelLower.tsum_eq]
  exact tsum_congr fun c => arithmeticDirichletTerm_conj s h c

theorem scatteringCoefficient_conj (s : ℂ) (h : O) :
    scatteringCoefficient (star s) (conjO h) = star (scatteringCoefficient s h) := by
  unfold scatteringCoefficient
  rw [arithmeticDirichletSeries_conj, star_div₀,
    show star (((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)) = ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) from Complex.conj_ofReal _]

/-! ### The Dirichlet series at the cusp `0` -/

theorem unramifiedNormWeight_conj (s : ℂ) (I : Ideal O) :
    unramifiedNormWeight (star s) (conjIdeal I) = star (unramifiedNormWeight s I) := by
  unfold unramifiedNormWeight
  simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  rw [primaryIdealGenerator_conj, absNorm_conjIdeal]
  by_cases h : primaryIdealGenerator I = 0
  · rw [if_pos (show conjO (primaryIdealGenerator I) = 0 by rw [h, map_zero]), if_pos h, star_zero]
  · rw [if_neg (conjO_ne_zero h), if_neg h, show -star s = star (-s) from (star_neg s).symm, natCast_cpow_star]

/-- Conjugation of good ideals. -/
def conjGoodIdeal : GoodIdeal ≃ GoodIdeal where
  toFun I := ⟨conjIdeal I.1, by rw [primaryIdealGenerator_conj]; exact conjO_ne_zero I.2⟩
  invFun I := ⟨conjIdeal I.1, by rw [primaryIdealGenerator_conj]; exact conjO_ne_zero I.2⟩
  left_inv I := Subtype.ext (conjIdeal_conjIdeal I.1)
  right_inv I := Subtype.ext (conjIdeal_conjIdeal I.1)

/-- **The Dirichlet series at `0` is conjugation symmetric.** -/
theorem unramifiedCubicGaussSeries_conj (s : ℂ) (h : O) :
    unramifiedCubicGaussSeries (star s) (conjO h) = star (unramifiedCubicGaussSeries s h) := by
  unfold unramifiedCubicGaussSeries
  rw [tsum_star, ← conjGoodIdeal.tsum_eq]
  refine tsum_congr fun I => ?_
  change unramifiedNormWeight (star s) (conjIdeal I.1) *
    cubicUnitGaussSum (conjO h) (primaryIdealGenerator (conjIdeal I.1)) = _
  rw [unramifiedNormWeight_conj, primaryIdealGenerator_conj, cubicUnitGaussSum_conj h _ I.2, star_mul']

end GaloisForLFunctions.OrderSixMetaplecticTheory
