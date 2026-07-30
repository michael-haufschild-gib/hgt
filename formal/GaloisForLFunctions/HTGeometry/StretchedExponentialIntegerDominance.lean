import GaloisForLFunctions.HTGeometry.StretchedExponentialMinimizerGap
import GaloisForLFunctions.HTGeometry.MagnitudeIntegerDominance

open Filter Finset PowerSeries MvPolynomial

namespace GaloisForLFunctions

noncomputable section

def tupleOfFinsupp (ν : ℕ →₀ ℕ) (D : ℕ)
    (hcount : ν.sum (fun _ k => k) = D) : Fin D → ℕ :=
  let m := Finsupp.toMultiset ν
  let hcard : Fintype.card m = D := by
    rw [Multiset.card_coe, Finsupp.card_toMultiset]
    simpa [Function.id_def] using hcount
  let e : Fin D ≃ m := (Fintype.equivFinOfCardEq hcard).symm
  fun i => (e i : ℕ)

lemma key_tupleOfFinsupp (ν : ℕ →₀ ℕ) (D : ℕ)
    (hcount : ν.sum (fun _ k => k) = D) :
    key (tupleOfFinsupp ν D hcount) = ν := by
  classical
  let m := Finsupp.toMultiset ν
  let hcard : Fintype.card m = D := by
    rw [Multiset.card_coe, Finsupp.card_toMultiset]
    simpa [Function.id_def] using hcount
  let e : Fin D ≃ m := (Fintype.equivFinOfCardEq hcard).symm
  have he : tupleOfFinsupp ν D hcount = fun i => (e i : ℕ) := by
    rfl
  rw [he]
  ext a
  rw [key_count_map]
  have hmap : Multiset.map (fun i : Fin D => ((e i : m) : ℕ))
      (Finset.univ : Finset (Fin D)).val = m := by
    have heuniv := congrArg Finset.val (Finset.map_univ_equiv e)
    rw [Finset.map_val] at heuniv
    calc
      Multiset.map (fun i : Fin D => ((e i : m) : ℕ))
          (Finset.univ : Finset (Fin D)).val =
        Multiset.map (fun x : m => (x : ℕ))
          (Multiset.map e (Finset.univ : Finset (Fin D)).val) := by
            rw [Multiset.map_map]
            simp only [Function.comp_apply]
      _ = Multiset.map (fun x : m => (x : ℕ))
          (Finset.univ : Finset m).val := congrArg _ heuniv
      _ = m := Multiset.map_univ_coe m
  calc
    Multiset.count a (Multiset.map (fun i : Fin D => ((e i : m) : ℕ))
        (Finset.univ : Finset (Fin D)).val) = Multiset.count a m := congrArg _ hmap
    _ = ν a := Finsupp.count_toMultiset ν a

lemma valuation_tupleOfFinsupp (ν : ℕ →₀ ℕ) (D : ℕ)
    (hcount : ν.sum (fun _ k => k) = D) (b : ℕ → ℝ) :
    ν.sum (fun i k => (k : ℝ) * b i) =
      ∑ i, b (tupleOfFinsupp ν D hcount i) := by
  calc
    ν.sum (fun i k => (k : ℝ) * b i) =
        (key (tupleOfFinsupp ν D hcount)).sum (fun i k => (k : ℝ) * b i) :=
      congrArg (fun μ : ℕ →₀ ℕ => μ.sum (fun i k => (k : ℝ) * b i))
        (key_tupleOfFinsupp ν D hcount).symm
    _ = ∑ i, b (tupleOfFinsupp ν D hcount i) := valuation_eq_key_sum _ _

lemma sum_tupleOfFinsupp (ν : ℕ →₀ ℕ) (D : ℕ)
    (hcount : ν.sum (fun _ k => k) = D) :
    ∑ i, tupleOfFinsupp ν D hcount i = ν.sum (fun i k => i * k) := by
  calc
    ∑ i, tupleOfFinsupp ν D hcount i =
        (key (tupleOfFinsupp ν D hcount)).sum (fun i k => i * k) :=
      (key_weighted_sum (tupleOfFinsupp ν D hcount)).symm
    _ = ν.sum (fun i k => i * k) :=
      congrArg (fun μ : ℕ →₀ ℕ => μ.sum (fun i k => i * k))
        (key_tupleOfFinsupp ν D hcount)

def magnitudeShiftCode (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (m : Fin (n + 2) →₀ ℕ) : ℕ :=
  magnitudeMaxJetOrder n Q + m 0 - jetMonomialOrder n m

lemma shiftCode_add_order {n : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {m : Fin (n + 2) →₀ ℕ} (hm : m ∈ Q.support) :
    magnitudeShiftCode n Q m + jetMonomialOrder n m =
      magnitudeMaxJetOrder n Q + m 0 := by
  rw [magnitudeShiftCode, Nat.sub_add_cancel]
  exact Nat.le_add_right_of_le (jetOrder_le_magnitudeMaxJetOrder Q hm)

lemma exists_maxShiftCode_topDegree_anchor {n : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hD : 0 < magnitudeMaxJetDegree n Q) :
    ∃ anchor ∈ Q.support,
      jetMonomialDegree n anchor = magnitudeMaxJetDegree n Q ∧
      ∀ m ∈ Q.support,
        jetMonomialDegree n m = magnitudeMaxJetDegree n Q →
          magnitudeShiftCode n Q m ≤ magnitudeShiftCode n Q anchor := by
  classical
  let D := magnitudeMaxJetDegree n Q
  have hsupport : Q.support.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have : D = 0 := by simp [D, magnitudeMaxJetDegree, hempty]
    omega
  obtain ⟨m₀, hm₀, hm₀D⟩ :=
    Finset.exists_mem_eq_sup Q.support hsupport (fun m => jetMonomialDegree n m)
  have hm₀top : jetMonomialDegree n m₀ = D := by
    dsimp [D]
    rw [magnitudeMaxJetDegree, jetMonomialDegree]
    exact hm₀D.symm
  let top := Q.support.filter fun m => jetMonomialDegree n m = D
  have htop : top.Nonempty := ⟨m₀, Finset.mem_filter.mpr ⟨hm₀, hm₀top⟩⟩
  obtain ⟨anchor, haTop, haMax⟩ :=
    Finset.exists_max_image top (magnitudeShiftCode n Q) htop
  have ha := (Finset.mem_filter.mp haTop).1
  have haD := (Finset.mem_filter.mp haTop).2
  refine ⟨anchor, ha, haD, ?_⟩
  intro m hm hmD
  exact haMax m (Finset.mem_filter.mpr ⟨hm, hmD⟩)

lemma appearing_atom_sum_add_shiftCode {n N : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {ν : ℕ →₀ ℕ}
    (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n)) :
    ∃ m ∈ Q.support,
      jetMonomialDegree n m = ν.sum (fun _ k => k) ∧
      ν.sum (fun i k => i * k) + magnitudeShiftCode n Q m =
        N + magnitudeMaxJetOrder n Q := by
  obtain ⟨x, hx, _hkey, hcount, hweight⟩ := atom_grading_witness_of_mem Q hν
  have hm : x.1 ∈ Q.support := by
    rw [sigmaIdx, Finset.mem_sigma] at hx
    exact (Finset.mem_filter.mp hx.1).1
  have hmN : x.1 0 ≤ N := by
    rw [sigmaIdx, Finset.mem_sigma] at hx
    exact (Finset.mem_filter.mp hx.1).2
  refine ⟨x.1, hm, hcount.symm, ?_⟩
  rw [hweight]
  have hcode := shiftCode_add_order Q hm
  omega

lemma witness_sum_add_shiftCode {n q : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {anchor : Fin (n + 2) →₀ ℕ}
    (ha : anchor ∈ Q.support) {D : ℕ}
    (δ : Fin D → ℕ)
    (N : ℕ) (hN : N = (∑ i : Fin D, (q + δ i)) + anchor 0 - jetMonomialOrder n anchor)
    (hq : jetMonomialOrder n anchor ≤ ∑ i : Fin D, (q + δ i)) :
    (∑ i : Fin D, (q + δ i)) + magnitudeShiftCode n Q anchor =
      N + magnitudeMaxJetOrder n Q := by
  have hNadd : N + jetMonomialOrder n anchor = (∑ i : Fin D, (q + δ i)) + anchor 0 := by
    rw [hN]
    omega
  have hcode := shiftCode_add_order Q ha
  omega

lemma stretchedExp_add_isLittleO_mul {α c B : ℝ}
    (hα0 : 0 < α) (hc : 1 < c) (hB : 0 ≤ B) :
    (fun x : ℝ => stretchedExp α (x + B)) =o[atTop]
      fun x => stretchedExp α (c * x) := by
  let a := (1 + c) / 2
  have ha1 : 1 < a := by dsimp [a]; linarith
  have hac : a < c := by dsimp [a]; linarith
  have ha0 : 0 < a := one_pos.trans ha1
  have hc0 : 0 < c := one_pos.trans hc
  let d := c ^ α - a ^ α
  have hd : 0 < d := by
    dsimp [d]
    exact sub_pos.mpr (Real.rpow_lt_rpow ha0.le hac hα0)
  have htbase : Tendsto (fun x : ℝ => d * x ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα0).const_mul_atTop hd
  have htlin : Tendsto (fun x : ℝ => (a - 1) * x) atTop atTop :=
    tendsto_id.const_mul_atTop (sub_pos.mpr ha1)
  have hBlin : ∀ᶠ x : ℝ in atTop, B ≤ (a - 1) * x := htlin.eventually_ge_atTop B
  change (fun x : ℝ => Real.exp ((x + B) ^ α)) =o[atTop]
    fun x => Real.exp ((c * x) ^ α)
  rw [Real.isLittleO_exp_comp_exp_comp]
  refine tendsto_atTop_mono' atTop ?_ htbase
  filter_upwards [eventually_gt_atTop (0 : ℝ), hBlin] with x hx hBx
  have hxB0 : 0 ≤ x + B := add_nonneg hx.le hB
  have hxa : x + B ≤ a * x := by linarith
  have hrpow : (x + B) ^ α ≤ (a * x) ^ α :=
    Real.rpow_le_rpow hxB0 hxa hα0.le
  rw [Real.mul_rpow ha0.le hx.le] at hrpow
  rw [Real.mul_rpow hc0.le hx.le]
  dsimp [d]
  linarith

lemma log_isLittleO_stretchedExp {α : ℝ} (hα0 : 0 < α) :
    Real.log =o[atTop] stretchedExp α := by
  have hrpowExp : (fun x : ℝ => x ^ α) =o[atTop] stretchedExp α := by
    have h := (Real.isLittleO_pow_exp_atTop (n := 1)).comp_tendsto
      (tendsto_rpow_atTop hα0)
    simpa [stretchedExp] using! h
  exact (isLittleO_log_rpow_atTop hα0).trans hrpowExp

lemma key_scaledStretchedValuation {α B : ℝ} {D : ℕ} (t : Fin D → ℕ) :
    (key t).sum (fun i k => (k : ℝ) * (B * stretchedExp α i)) =
      B * tupleStretchedValuation α t := by
  rw [valuation_eq_key_sum]
  rw [tupleStretchedValuation, Finset.mul_sum]

lemma stretchedExp_mono_of_nonneg {α x y : ℝ} (hα0 : 0 < α)
    (hx : 0 ≤ x) (hxy : x ≤ y) : stretchedExp α x ≤ stretchedExp α y := by
  rw [stretchedExp, stretchedExp]
  exact Real.exp_le_exp.mpr (Real.rpow_le_rpow hx hxy hα0.le)

lemma lowerDegree_factor_le {D : ℕ} (hD : 0 < D) :
    ((D : ℝ) - 1) * (1 + 1 / (2 * (D : ℝ))) ≤ (D : ℝ) - 1 / 2 := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  field_simp
  nlinarith

/-- Positive-degree integer dominance for stretched-exponential Taylor magnitudes. -/
theorem exists_stretchedExponential_intDominance_of_positiveJetDegree
    {α B : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hB : 0 < B)
    {n : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hDpos : 0 < magnitudeMaxJetDegree n Q) :
    ∃ (N : ℕ) (ν₀ : ℕ →₀ ℕ) (G : ℝ),
      ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
      aevalWeight n N Q ν₀ ≠ 0 ∧
      (∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        aevalWeight n N Q ν ≠ 0 → ν ≠ ν₀ →
          ν₀.sum (fun i k => (k : ℝ) * (B * stretchedExp α i)) + G ≤
            ν.sum (fun i k => (k : ℝ) * (B * stretchedExp α i))) ∧
      (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖) <
        Real.exp G := by
  classical
  let O := magnitudeMaxJetOrder n Q
  let Z := magnitudeMaxXDegree Q
  obtain ⟨anchor, ha, haD, haMax⟩ :=
    exists_maxShiftCode_topDegree_anchor Q hDpos
  let D := jetMonomialDegree n anchor
  let E := D + O
  let M := E + 1
  have haD' : D = magnitudeMaxJetDegree n Q := by simpa [D] using haD
  have hD : 0 < D := by rw [haD']; exact hDpos
  have haPos : 0 < jetMonomialDegree n anchor := by simpa [D] using hD
  obtain ⟨δ, _hδinj, Qbal, hbalanced⟩ :=
    exists_eventually_balanced_nonzero_aevalWeight ha haPos
  let J := jetMonomialOrder n anchor
  let Boff := magnitudeOffsetMax δ
  let Csum := magnitudeShiftCode n Q anchor
  let Cgap : ℝ := (M : ℝ) / B
  have hM : 0 < M := by dsimp [M, E]; omega
  have hCgap : 0 < Cgap := div_pos (by exact_mod_cast hM) hB
  obtain ⟨K, hgeom⟩ :=
    exists_eventually_logGap_stretchedMinimizer hα0 hα1 hCgap hD δ Csum
  let GeomProp := fun q : ℕ => ∀ (A : Finset (Fin D → ℕ)),
    (fun i => q + δ i) ∈ A →
    (∀ t ∈ A, D * q + (∑ i, δ i) ≤ ∑ i, t i ∧
      (∑ i, t i) ≤ D * q + (∑ i, δ i) + Csum) →
    ∀ t ∈ A,
      (∀ r ∈ A, tupleStretchedValuation α t ≤ tupleStretchedValuation α r) →
      tupleInWindow q K t ∧
      ∀ r ∈ A, key r ≠ key t →
        Cgap * Real.log ((q : ℝ) - (K + 1)) <
          tupleStretchedValuation α r - tupleStretchedValuation α t
  have hgeomP : ∀ᶠ q : ℕ in atTop, GeomProp q := by
    simpa [GeomProp] using hgeom
  let L := K + 1
  let Aconst : ℝ :=
    magnitudeCoefficientMass Q * (((O + 1) ^ O : ℕ) : ℝ)
  have hCoeffMass : 0 < magnitudeCoefficientMass Q := by
    rw [magnitudeCoefficientMass]
    exact Finset.sum_pos' (fun _ _ => norm_nonneg _)
      ⟨anchor, ha, norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp ha)⟩
  have hAconst : 0 < Aconst := by
    dsimp [Aconst]
    exact mul_pos hCoeffMass (by positivity)
  let Llevel := D * (Boff + 1) + anchor 0 + 1
  let Cmass := 2 * Llevel
  have hLlevel : 0 < Llevel := by dsimp [Llevel]; omega
  have hCmass : 0 < Cmass := by dsimp [Cmass]; omega
  have hscaleReal := stretchedExp_add_isLittleO_mul hα0
    (show (1 : ℝ) < 1 + 1 / (2 * (D : ℝ)) by
      apply lt_add_of_pos_right
      exact div_pos one_pos (mul_pos (by norm_num) (by exact_mod_cast hD)))
    (show (0 : ℝ) ≤ (Boff : ℝ) by positivity)
  have hscalePos : ∀ᶠ x : ℝ in atTop,
      0 < ‖stretchedExp α ((1 + 1 / (2 * (D : ℝ))) * x)‖ :=
    Filter.Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs, abs_pos]
      exact (Real.exp_pos _).ne'
  have hscaleGapReal :=
    (hscaleReal.const_mul_left ((D : ℝ) + Cgap)).eventuallyLT_norm_of_eventually_pos
      hscalePos
  have hscaleGap : ∀ᶠ q : ℕ in atTop,
      ((D : ℝ) + Cgap) * stretchedExp α ((q : ℝ) + Boff) <
        stretchedExp α ((1 + 1 / (2 * (D : ℝ))) * q) := by
    have hnat := tendsto_natCast_atTop_atTop.eventually hscaleGapReal
    filter_upwards [hnat] with q hq
    simp only [stretchedExp] at hq ⊢
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),
      abs_of_pos (mul_pos (add_pos (by exact_mod_cast hD) hCgap) (Real.exp_pos _))] at hq
    simpa [Nat.cast_add] using hq
  have hlogReal := (log_isLittleO_stretchedExp hα0).eventuallyLT_norm_of_eventually_pos
    (Filter.Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs, abs_pos]
      exact (Real.exp_pos _).ne')
  have hlog : ∀ᶠ q : ℕ in atTop,
      Real.log q < stretchedExp α q := by
    have hnat := tendsto_natCast_atTop_atTop.eventually hlogReal
    filter_upwards [hnat, eventually_ge_atTop 2] with q hq hq2
    have hqreal : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
    simp only [stretchedExp] at hq ⊢
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.log_pos hqreal),
      abs_of_pos (Real.exp_pos _)] at hq
    exact hq
  have hbase : Tendsto (fun q : ℕ => (q : ℝ) - L) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(L : ℝ)) tendsto_natCast_atTop_atTop
  have hlargeMass : ∀ᶠ q : ℕ in atTop,
      Aconst * (Cmass : ℝ) ^ E < (q : ℝ) - L :=
    hbase.eventually_gt_atTop (Aconst * (Cmass : ℝ) ^ E)
  have hevent : ∀ᶠ q : ℕ in atTop,
      Qbal ≤ q ∧ GeomProp q ∧
      ((D : ℝ) + Cgap) * stretchedExp α ((q : ℝ) + Boff) <
        stretchedExp α ((1 + 1 / (2 * (D : ℝ))) * q) ∧
      Real.log q < stretchedExp α q ∧
      Aconst * (Cmass : ℝ) ^ E < (q : ℝ) - L ∧
      max (2 * L + 2) (2 * (J + Z) + 2) ≤ q := by
    filter_upwards [eventually_ge_atTop Qbal, hgeomP, hscaleGap, hlog, hlargeMass,
      eventually_ge_atTop (max (2 * L + 2) (2 * (J + Z) + 2))] with
      q hqbal hqgeom hqscale hqlog hqlarge hqthreshold
    exact ⟨hqbal, hqgeom, hqscale, hqlog, hqlarge, hqthreshold⟩
  obtain ⟨q, hqbal, hqgeom, hqscale, hqlog, hqlarge, hqthreshold⟩ := hevent.exists
  let s : Fin (jetMonomialDegree n anchor) → ℕ := fun i => q + δ i
  let N := (∑ i, s i) + anchor 0 - J
  have hqJ : J ≤ q := by
    have : J ≤ J + Z := Nat.le_add_right _ _
    omega
  have hqsum : q ≤ ∑ i, s i :=
    le_sum_of_le_apply haPos fun i => by simp [s]
  have hJsum : J ≤ (∑ i, s i) + anchor 0 :=
    hqJ.trans (hqsum.trans (Nat.le_add_right _ _))
  have hNadd : N + J = (∑ i, s i) + anchor 0 := by
    dsimp [N]
    exact Nat.sub_add_cancel hJsum
  have hsLower : D * q ≤ ∑ i, s i :=
    mul_le_sum_of_le_apply fun i => by simp [s]
  have hDqN : D * q ≤ N + J := by rw [hNadd]; omega
  have hNZ : Z < N := by
    have hqJZ : J + Z < q := by omega
    have hqD : q ≤ D * q := by
      simpa [one_mul] using Nat.mul_le_mul_right q (show 1 ≤ D by omega)
    omega
  obtain ⟨hνw, hww, _hgroup⟩ :
      key s ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
        aevalWeight n N Q (key s) ≠ 0 ∧
        balancedJetGroup n N (jetMonomialDegree n anchor) Q s =
          topShiftJetGroup n Q anchor := by
    simpa only [s, N, J] using hbalanced q hqbal
  let topKeys := ((sigmaIdx n N Q).image (atomKeyOf n)).filter fun ν =>
    aevalWeight n N Q ν ≠ 0 ∧ ν.sum (fun _ k => k) = D
  have hwTop : key s ∈ topKeys := by
    rw [Finset.mem_filter]
    refine ⟨hνw, hww, ?_⟩
    rw [key_total_count]
  let tupleSet : Finset (Fin D → ℕ) :=
    topKeys.attach.image fun ν =>
      tupleOfFinsupp ν.1 D ((Finset.mem_filter.mp ν.2).2.2)
  let A : Finset (Fin D → ℕ) := insert (fun i => q + δ i) tupleSet
  have hwA : (fun i => q + δ i) ∈ A := Finset.mem_insert_self _ _
  have hAne : A.Nonempty := ⟨_, hwA⟩
  obtain ⟨t₀, ht₀A, ht₀min⟩ :=
    A.exists_min_image (tupleStretchedValuation α) hAne
  have hAbounds : ∀ t ∈ A,
      D * q + (∑ i, δ i) ≤ ∑ i, t i ∧
      (∑ i, t i) ≤ D * q + (∑ i, δ i) + Csum := by
    intro t ht
    rw [Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · have heq : (∑ i : Fin D, (q + δ i)) = D * q + ∑ i : Fin D, δ i := by
        rw [Finset.sum_add_distrib]
        simp [D, Nat.mul_comm]
      rw [heq]
      exact ⟨le_rfl, Nat.le_add_right _ _⟩
    · obtain ⟨νsub, _hνattach, htν⟩ := Finset.mem_image.mp ht
      subst t
      have hνtop := νsub.2
      have hνmem := (Finset.mem_filter.mp hνtop).1
      have hνcount := (Finset.mem_filter.mp hνtop).2.2
      obtain ⟨m, hm, hmD, hinv⟩ := appearing_atom_sum_add_shiftCode Q hνmem
      have hmTop : jetMonomialDegree n m = magnitudeMaxJetDegree n Q := by
        rw [hmD, hνcount]
        exact haD'
      have hcodele := haMax m hm hmTop
      have hwitinv := witness_sum_add_shiftCode Q ha δ N rfl (hqJ.trans hqsum)
      have hsumt := sum_tupleOfFinsupp νsub.1 D hνcount
      have hsEq : (∑ i, s i) = D * q + ∑ i, δ i := by
        simp [s, D, Finset.sum_add_distrib]
      change (νsub.1.sum fun i k => i * k) + magnitudeShiftCode n Q m = N + O at hinv
      change (∑ i, s i) + Csum = N + O at hwitinv
      change magnitudeShiftCode n Q m ≤ Csum at hcodele
      constructor
      · rw [hsumt]
        omega
      · rw [hsumt]
        omega
  obtain ⟨ht₀wide, ht₀gap⟩ := hqgeom A hwA hAbounds t₀ ht₀A ht₀min
  have ht₀data :
      key t₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
      aevalWeight n N Q (key t₀) ≠ 0 ∧
      (key t₀).sum (fun _ k => k) = D := by
    rw [Finset.mem_insert] at ht₀A
    rcases ht₀A with htEq | htImage
    · subst t₀
      exact ⟨hνw, hww, by rw [key_total_count]⟩
    · obtain ⟨νsub, _hattach, htEq⟩ := Finset.mem_image.mp htImage
      subst t₀
      have hνtop := νsub.2
      have hνfilter := Finset.mem_filter.mp hνtop
      rw [key_tupleOfFinsupp νsub.1 D hνfilter.2.2]
      exact ⟨hνfilter.1, hνfilter.2.1, hνfilter.2.2⟩
  obtain ⟨hν₀, hw₀, hν₀count⟩ := ht₀data
  let ν₀ := key t₀
  let G := (M : ℝ) * Real.log ((q : ℝ) - L)
  have hBCgap : B * Cgap = (M : ℝ) := by
    dsimp [Cgap]
    field_simp
  have hgapAll : ∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
      aevalWeight n N Q ν ≠ 0 → ν ≠ ν₀ →
        ν₀.sum (fun i k => (k : ℝ) * (B * stretchedExp α i)) + G ≤
          ν.sum (fun i k => (k : ℝ) * (B * stretchedExp α i)) := by
    intro ν hν hw hne
    have hcountle := appearing_atom_count_le Q hν
    change ν.sum (fun _ k => k) ≤ magnitudeMaxJetDegree n Q at hcountle
    rw [← haD'] at hcountle
    rcases hcountle.eq_or_lt with hcountEq | hcountLt
    · have hcount : ν.sum (fun _ k => k) = D := hcountEq
      let νsub : ↥topKeys := ⟨ν, Finset.mem_filter.mpr ⟨hν, hw, hcount⟩⟩
      let t : Fin D → ℕ := tupleOfFinsupp ν D hcount
      have htTuple : t ∈ tupleSet := by
        apply Finset.mem_image.mpr
        refine ⟨νsub, Finset.mem_attach _ νsub, ?_⟩
        rfl
      have htA : t ∈ A := Finset.mem_insert_of_mem htTuple
      have hkeyt : key t = ν := key_tupleOfFinsupp ν D hcount
      have hkeyne : key t ≠ key t₀ := by
        rw [hkeyt]
        simpa [ν₀] using hne
      have hgap := ht₀gap t htA hkeyne
      have hgap' : Cgap * Real.log ((q : ℝ) - L) <
          tupleStretchedValuation α t - tupleStretchedValuation α t₀ := by
        simpa [L, Nat.cast_add] using hgap
      have hscaled := mul_lt_mul_of_pos_left hgap' hB
      have hscaled' : (M : ℝ) * Real.log ((q : ℝ) - L) <
          B * (tupleStretchedValuation α t - tupleStretchedValuation α t₀) := by
        calc
          (M : ℝ) * Real.log ((q : ℝ) - L) =
              B * (Cgap * Real.log ((q : ℝ) - L)) := by rw [← hBCgap]; ring
          _ < _ := hscaled
      change (key t₀).sum (fun i k => (k : ℝ) * (B * stretchedExp α i)) +
          (M : ℝ) * Real.log ((q : ℝ) - L) ≤
        ν.sum (fun i k => (k : ℝ) * (B * stretchedExp α i))
      rw [← hkeyt, key_scaledStretchedValuation, key_scaledStretchedValuation]
      linarith
    · have hcountSmall : ν.sum (fun _ k => k) ≤ D - 1 := by omega
      have hsupport := appearing_atom_support_nonempty_of_maxX_lt_level Q hν hNZ
      by_cases hDone : D = 1
      · have hcountZero : ν.sum (fun _ k => k) = 0 := by omega
        obtain ⟨i, hi⟩ := hsupport
        have hiBound := finsupp_apply_le_count ν i
        rw [hcountZero] at hiBound
        have hiNe : ν i ≠ 0 := Finsupp.mem_support_iff.mp hi
        exact False.elim (hiNe (Nat.eq_zero_of_le_zero hiBound))
      · have hDtwo : 2 ≤ D := by omega
        let imax := ν.support.max' hsupport
        have hweightLower := (appearing_atom_weighted_sum_bounds Q hν).1
        change N - Z ≤ ν.sum (fun i k => i * k) at hweightLower
        have hweightMax := weighted_sum_le_max_mul_count hsupport
        have hDqMax : D * q ≤ imax * (D - 1) + J + Z := by
          have hweightUpper : ν.sum (fun i k => i * k) ≤ imax * (D - 1) := by
            exact hweightMax.trans (Nat.mul_le_mul_left imax hcountSmall)
          have hNsplit : N - Z + Z = N := Nat.sub_add_cancel hNZ.le
          omega
        let c : ℝ := 1 + 1 / (2 * (D : ℝ))
        have hcMax : c * (q : ℝ) ≤ (imax : ℝ) := by
          by_contra hnot
          have hlt : (imax : ℝ) < c * (q : ℝ) := lt_of_not_ge hnot
          have hDsub : (((D - 1 : ℕ) : ℝ)) = (D : ℝ) - 1 := by
            rw [Nat.cast_sub (show 1 ≤ D by omega)]
            norm_num
          have hmul : (imax : ℝ) * ((D - 1 : ℕ) : ℝ) <
              (c * (q : ℝ)) * ((D - 1 : ℕ) : ℝ) :=
            mul_lt_mul_of_pos_right hlt (by exact_mod_cast (show 0 < D - 1 by omega))
          have hfactor : (((D - 1 : ℕ) : ℝ)) * c ≤ (D : ℝ) - 1 / 2 := by
            rw [hDsub]
            exact lowerDegree_factor_le hD
          have hfactorq : (((D - 1 : ℕ) : ℝ)) * c * (q : ℝ) ≤
              ((D : ℝ) - 1 / 2) * (q : ℝ) := by
            exact mul_le_mul_of_nonneg_right hfactor (by positivity)
          have hthreshold : 2 * (J + Z) + 2 ≤ q :=
            (le_max_right _ _).trans hqthreshold
          have hJZtwo : (2 : ℝ) * ((J + Z : ℕ) : ℝ) < (q : ℝ) := by
            have hnat : 2 * (J + Z) < q := by omega
            exact_mod_cast hnat
          have hJZ : ((J + Z : ℕ) : ℝ) < (q : ℝ) / 2 := by linarith
          have hDqMaxR : (D : ℝ) * q ≤
              (imax : ℝ) * ((D - 1 : ℕ) : ℝ) + J + Z := by
            exact_mod_cast hDqMax
          have hupper : (imax : ℝ) * ((D - 1 : ℕ) : ℝ) + J + Z <
              (D : ℝ) * q := by
            calc
              (imax : ℝ) * ((D - 1 : ℕ) : ℝ) + J + Z <
                  (c * (q : ℝ)) * ((D - 1 : ℕ) : ℝ) + J + Z := by linarith
              _ = (((D - 1 : ℕ) : ℝ) * c) * (q : ℝ) + (J + Z : ℕ) := by
                push_cast
                ring
              _ ≤ ((D : ℝ) - 1 / 2) * (q : ℝ) + (J + Z : ℕ) := by
                gcongr
              _ < (D : ℝ) * q := by linarith
          exact (not_lt_of_ge hDqMaxR) hupper
        have hstretchMax : stretchedExp α (c * (q : ℝ)) ≤
            stretchedExp α imax :=
          stretchedExp_mono_of_nonneg hα0 (by positivity) hcMax
        have hvalMax := valuation_ge_b_max
          (b := fun i : ℕ => stretchedExp α i)
          (fun i => (Real.exp_pos _).le) hsupport
        have hcompVal : stretchedExp α (c * (q : ℝ)) ≤
            ν.sum (fun i k => (k : ℝ) * stretchedExp α i) :=
          hstretchMax.trans hvalMax
        have hWval : tupleStretchedValuation α (fun i : Fin D => q + δ i) ≤
            (D : ℝ) * stretchedExp α ((q : ℝ) + Boff) := by
          rw [tupleStretchedValuation]
          simp_rw [Nat.cast_add]
          calc
            (∑ i : Fin D, stretchedExp α ((q : ℝ) + δ i)) ≤
                ∑ _i : Fin D, stretchedExp α ((q : ℝ) + Boff) := by
              apply Finset.sum_le_sum
              intro i _
              apply stretchedExp_mono_of_nonneg hα0 (by positivity)
              exact_mod_cast Nat.add_le_add_left (offset_le_magnitudeOffsetMax δ i) q
            _ = (D : ℝ) * stretchedExp α ((q : ℝ) + Boff) := by simp
        have ht₀upper : tupleStretchedValuation α t₀ ≤
            (D : ℝ) * stretchedExp α ((q : ℝ) + Boff) :=
          (ht₀min _ hwA).trans hWval
        have hxpos : 0 < (q : ℝ) - L := by
          have hLq : L < q := by omega
          have hLqR : (L : ℝ) < q := by exact_mod_cast hLq
          linarith
        have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
        have hlogxq : Real.log ((q : ℝ) - L) ≤ Real.log q := by
          rw [Real.log_le_log_iff hxpos hqpos]
          linarith
        have hstretchShift : stretchedExp α (q : ℝ) ≤
            stretchedExp α ((q : ℝ) + Boff) :=
          stretchedExp_mono_of_nonneg hα0 (Nat.cast_nonneg q)
            (le_add_of_nonneg_right (Nat.cast_nonneg Boff))
        have hlogShift : Real.log ((q : ℝ) - L) <
            stretchedExp α ((q : ℝ) + Boff) :=
          hlogxq.trans_lt (hqlog.trans_le hstretchShift)
        have hbaseGap : tupleStretchedValuation α t₀ +
            Cgap * Real.log ((q : ℝ) - L) <
              ν.sum (fun i k => (k : ℝ) * stretchedExp α i) := by
          have hlogScaled := mul_lt_mul_of_pos_left hlogShift hCgap
          have hmid : tupleStretchedValuation α t₀ +
              Cgap * Real.log ((q : ℝ) - L) <
                ((D : ℝ) + Cgap) * stretchedExp α ((q : ℝ) + Boff) := by
            nlinarith
          exact hmid.trans (hqscale.trans_le hcompVal)
        have hscaled := mul_lt_mul_of_pos_left hbaseGap hB
        have hscaled' : B * tupleStretchedValuation α t₀ +
            (M : ℝ) * Real.log ((q : ℝ) - L) <
              B * ν.sum (fun i k => (k : ℝ) * stretchedExp α i) := by
          calc
            B * tupleStretchedValuation α t₀ +
                (M : ℝ) * Real.log ((q : ℝ) - L) =
              B * (tupleStretchedValuation α t₀ +
                Cgap * Real.log ((q : ℝ) - L)) := by rw [← hBCgap]; ring
            _ < _ := hscaled
        change (key t₀).sum (fun i k => (k : ℝ) * (B * stretchedExp α i)) +
            (M : ℝ) * Real.log ((q : ℝ) - L) ≤
          ν.sum (fun i k => (k : ℝ) * (B * stretchedExp α i))
        rw [key_scaledStretchedValuation]
        have hνscale : ν.sum (fun i k => (k : ℝ) * (B * stretchedExp α i)) =
            B * ν.sum (fun i k => (k : ℝ) * stretchedExp α i) := by
          simp only [Finsupp.sum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hνscale]
        linarith
  have hsUpper : (∑ i, s i) ≤ D * (q + Boff) :=
    sum_le_mul_of_apply_le fun i => by
      dsimp [s]
      exact Nat.add_le_add_left (offset_le_magnitudeOffsetMax δ i) q
  have hNupper : N + 1 ≤ D * (q + Boff) + anchor 0 + 1 := by
    dsimp [N]
    omega
  have hlevel : N + 1 ≤ Llevel * (q + 1) := by
    have hbaseNat : q + Boff ≤ (Boff + 1) * (q + 1) := by
      calc
        q + Boff ≤ q + Boff + (Boff * q + 1) := Nat.le_add_right _ _
        _ = (Boff + 1) * (q + 1) := by ring
    have hjet : D * (q + Boff) ≤ D * (Boff + 1) * (q + 1) := by
      calc
        D * (q + Boff) ≤ D * ((Boff + 1) * (q + 1)) :=
          Nat.mul_le_mul_left D hbaseNat
        _ = D * (Boff + 1) * (q + 1) := by ring
    have hconst : anchor 0 + 1 ≤ (anchor 0 + 1) * (q + 1) := by
      calc
        anchor 0 + 1 ≤ (anchor 0 + 1) + (anchor 0 + 1) * q := Nat.le_add_right _ _
        _ = (anchor 0 + 1) * (q + 1) := by ring
    calc
      N + 1 ≤ D * (q + Boff) + anchor 0 + 1 := hNupper
      _ = D * (q + Boff) + (anchor 0 + 1) := by ring
      _ ≤ D * (Boff + 1) * (q + 1) + (anchor 0 + 1) * (q + 1) :=
        Nat.add_le_add hjet hconst
      _ = Llevel * (q + 1) := by dsimp [Llevel]; ring
  have hLq : L ≤ q := by omega
  have hqx : q + 1 ≤ 2 * (q - L) := by omega
  have hlevelX : N + 1 ≤ Cmass * (q - L) := by
    calc
      N + 1 ≤ Llevel * (q + 1) := hlevel
      _ ≤ Llevel * (2 * (q - L)) := Nat.mul_le_mul_left Llevel hqx
      _ = Cmass * (q - L) := by dsimp [Cmass]; ring
  have hxpos : 0 < (q : ℝ) - L := by
    have hLq' : L < q := by omega
    have hcast : (L : ℝ) < q := by exact_mod_cast hLq'
    linarith
  have hlevelXR : ((N + 1 : ℕ) : ℝ) ≤
      (Cmass : ℝ) * ((q : ℝ) - L) := by
    have hcast : ((N + 1 : ℕ) : ℝ) ≤ ((Cmass * (q - L) : ℕ) : ℝ) := by
      exact_mod_cast hlevelX
    push_cast at hcast
    rw [Nat.cast_sub hLq] at hcast
    simpa only [Nat.cast_add, Nat.cast_one] using hcast
  have hmassPoly :
      (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖) ≤
        Aconst * (((N + 1) ^ E : ℕ) : ℝ) := by
    simpa [Aconst, O, E, haD'] using aevalWeight_mass_le_singlePolynomial n Q N
  have hmass :
      (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖) <
        Real.exp G := by
    calc
      (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖)
          ≤ Aconst * (((N + 1) ^ E : ℕ) : ℝ) := hmassPoly
      _ = Aconst * (((N + 1 : ℕ) : ℝ) ^ E) := by push_cast; rfl
      _ ≤ Aconst * ((Cmass : ℝ) * ((q : ℝ) - L)) ^ E := by
        apply mul_le_mul_of_nonneg_left _ hAconst.le
        exact pow_le_pow_left₀ (by positivity) hlevelXR E
      _ = (Aconst * (Cmass : ℝ) ^ E) * (((q : ℝ) - L) ^ E) := by
        rw [mul_pow]
        ring
      _ < ((q : ℝ) - L) * (((q : ℝ) - L) ^ E) :=
        mul_lt_mul_of_pos_right hqlarge (pow_pos hxpos E)
      _ = ((q : ℝ) - L) ^ M := by
        dsimp [M]
        rw [pow_succ]
        ring
      _ = Real.exp G := by
        dsimp [G]
        rw [Real.exp_nat_mul, Real.exp_log hxpos]
  exact ⟨N, ν₀, G, by simpa [ν₀] using hν₀, by simpa [ν₀] using hw₀,
    hgapAll, hmass⟩

/-- Integer dominance for every nonzero polynomial at stretched-exponential magnitude profile. -/
theorem exists_stretchedExponential_intDominance
    {α B : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hB : 0 < B)
    {n : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ) (hQ : Q ≠ 0) :
    ∃ (N : ℕ) (ν₀ : ℕ →₀ ℕ) (G : ℝ),
      ν₀ ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
      aevalWeight n N Q ν₀ ≠ 0 ∧
      (∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        aevalWeight n N Q ν ≠ 0 → ν ≠ ν₀ →
          ν₀.sum (fun i k => (k : ℝ) * (B * stretchedExp α i)) + G ≤
            ν.sum (fun i k => (k : ℝ) * (B * stretchedExp α i))) ∧
      (∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖) <
        Real.exp G := by
  rcases Nat.eq_zero_or_pos (magnitudeMaxJetDegree n Q) with hzero | hpos
  · exact exists_intDominance_of_zeroJetDegree Q hQ hzero
  · exact exists_stretchedExponential_intDominance_of_positiveJetDegree
      hα0 hα1 hB Q hpos

end

end GaloisForLFunctions
