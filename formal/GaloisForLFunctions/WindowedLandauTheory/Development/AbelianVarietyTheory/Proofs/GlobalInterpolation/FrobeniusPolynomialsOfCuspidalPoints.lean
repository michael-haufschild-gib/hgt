import GaloisForLFunctions.WindowedLandauTheory.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsobaricCharacterTwist

/-! The split Hecke polynomial at a cuspidal point factors into the
normalized cuspidal polynomial and the known cyclotomic character factors. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.MainNotions.N ReciprocityTheory.Gal

namespace WindowedLandauTheory.NormalizedTypes

variable {R : Ranks} {H : Host R} {rows : Rows.Data R}
variable (N : NData R H rows) (A : NAut N)

private theorem galPol_tw_sum {w : PlE H} (a b : A.LP w)
    (ha : A.unr a) (hb : A.unr b) (s : ℝ) :
    galPol A (A.lpTw (A.lpSum a b) s) = galPol A (A.lpTw a s) * galPol A (A.lpTw b s) := by
  rw [A.lpTw_sum]
  unfold galPol
  rw [A.frobEig_sum _ _ ((A.unr_tw _ _).mpr ha) ((A.unr_tw _ _).mpr hb),
    Multiset.map_add, Multiset.prod_add]

private theorem galPol_tw_foldr {w : PlE H} (a : A.LP w) (ha : A.unr a)
    (e : ℕ → ℝ) (s : ℝ) (L : List ℕ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) ∧
    galPol A (A.lpTw (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) s) =
      (L.map fun k => galPol A (A.lpTw a (e k + s))).prod := by
  induction L with
  | nil =>
    refine ⟨A.lpZero_unr w, ?_⟩
    simp only [List.foldr_nil, List.map_nil, List.prod_nil, galPol,
      A.frobEig_tw _ _ (A.lpZero_unr w), A.frobEig_zero, Multiset.map_zero, Multiset.prod_zero]
  | cons k L ih =>
    have hk := (A.unr_tw a (e k)).mpr ha
    refine ⟨(A.unr_sum _ _).mpr ⟨hk, ih.1⟩, ?_⟩
    rw [List.foldr_cons, galPol_tw_sum N A _ _ hk ih.1 s, ih.2, A.lpTw_add,
      List.map_cons, List.prod_cons]

private theorem galPol_speh (p : Part A.CG) (w : PlE H)
    (ha : A.unr (A.locG p.π w)) (s : ℝ) :
    A.unr (spehLoc N A p w) ∧ galPol A (A.lpTw (spehLoc N A p w) s) =
      ∏ k ∈ Finset.range p.d, galPol A (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + s)) := by
  rw [spehLoc_eq_foldr]
  have h := galPol_tw_foldr N A _ ha (fun k => ((p.d : ℝ) - 1) / 2 - k) s (List.range p.d)
  refine ⟨h.1, h.2.trans ?_⟩
  rw [← List.prod_toFinset _ List.nodup_range, List.toFinset_range]

private theorem galPol_character_block (i : N.Loc) {w : PlE H} (hw : SplitOut N i w)
    {B : ValuationSubring N.Om} {σ : ConjugateSelfDual.G H.E N.Om}
    (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) (s : ℝ) :
    galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
      (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + s)) =
      X - C (iotaO N A i (N.chi i 1 σ : N.O i) * (normV w : ℂ) ^ (s : ℂ)) := by
  obtain ⟨hu, hχ⟩ := A.chi_mu i w hw
  unfold galPol
  rw [← A.lpTw_add, A.frobEig_tw _ _ ((A.unr_tw _ _).mpr hu), hχ B σ hB hσ]
  simp only [Multiset.map_singleton, Multiset.prod_singleton] <;> rfl

private theorem iota_chi_at_frobenius (i : N.Loc) {w : PlE H}
    (hw : w ∉ placesOver H.E (N.l i)) {B : ValuationSubring N.Om} {σ : ConjugateSelfDual.G H.E N.Om}
    (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ)
    {k : ℕ} (hk : k < R.t) :
    iotaO N A i (N.chi i (k + 1) σ : N.O i) =
      iotaO N A i (N.chi i 1 σ : N.O i) * (normV w : ℂ) ^ (-(k : ℝ) : ℂ) := by
  let p := N.l i
  letI : Fact p.Prime := N.lPrime i
  let ε := (Units.map (algebraMap ℤ_[p] (N.O i)).toMonoidHom).comp (cycZ H.E N.Om p)
  have he : iotaO N A i (ε σ : N.O i) = (normV w : ℂ) := by
    change iotaO N A i (algebraMap ℤ_[p] (N.O i) (cycZ H.E N.Om p σ : ℤ_[p])) = _
    have hq := cycZ_of_isFrob (show (p : 𝓞 H.E) ∉ w.asIdeal from hw) hB hσ
    rw [hq, map_natCast, map_natCast]
  have hχ : N.chi i (k + 1) = N.chi i 1 * ε ^ (-(k : ℤ)) := by
    rw [N.chi_def i (k + 1) (by omega) (by omega)]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] <;> rfl
  have hepow : iotaO N A i ((ε σ ^ (-(k : ℤ)) : (N.O i)ˣ) : N.O i) =
      (normV w : ℂ) ^ (-(k : ℝ) : ℂ) := by
    change ((Units.map (iotaO N A i).toMonoidHom (ε σ ^ (-(k : ℤ)))) : ℂ) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    change (iotaO N A i (ε σ : N.O i)) ^ (-(k : ℤ)) = _
    rw [he, ← Complex.cpow_intCast]
    simp only [Int.cast_neg, Int.cast_natCast, Complex.ofReal_natCast]
  rw [hχ, MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, map_mul, hepow]

/-- At a split prime outside the level, the auxiliary Speh block contributes
one linear factor per cyclotomic twist, with the normalized signs. -/
theorem hecke_polynomial_of_cuspidal_point (i : N.Loc) (x : N.X i)
    (π : A.CG R.r) (P : A.AV i) (hx : A.ptV i P = some x) {w : PlE H} (hw : SplitOut N i w)
    (hP : isoLoc N A (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv) w =
      A.locV i P w)
    (hu : A.unr (A.locG π w)) {B : ValuationSubring N.Om} {σ : ConjugateSelfDual.G H.E N.Om}
    (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    (heckePol N i x w).map (iotaO N A i) =
      galPol A (A.lpTw (A.locG (A.tw π A.etaTinv) w) ((1 - (R.nV : ℝ)) / 2)) *
        ∏ k : Fin R.t, (X - C (iotaO N A i (N.chi i ((k : ℕ) + 1) σ : N.O i))) := by
  let s := (1 - (R.nV : ℝ)) / 2
  let b : Part A.CG := ⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩
  have h₁ : A.unr (A.locG (A.tw π A.etaTinv) w) := by
    rw [A.locG_tw]
    exact A.unr_char _ _ (A.locG_dim _ _) hu (A.etaTinv_def w).1
  have h₂ := galPol_speh N A b w (A.chi_mu i w hw).1 s
  have hpt := A.pt_loc i P x hx w hw
  change (heckePol N i x w).map (iotaO N A i) = _ at hpt
  rw [hpt, ← hP]
  change galPol A (A.lpTw (A.lpSum
    (spehLoc N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w)
    (A.lpSum (spehLoc N A b w) (A.lpZero w))) s) = _
  have hspec : spehLoc N A ⟨R.r, A.tw π A.etaTinv, 1⟩ w = A.locG (A.tw π A.etaTinv) w := by
    simp [spehLoc_eq_foldr, List.range_succ, A.lpTw_zero, A.lpSum_zero]
  rw [hspec, A.lpSum_zero, galPol_tw_sum N A _ _ h₁ h₂.1 s, h₂.2]
  congr 1
  rw [Finset.prod_range]
  refine Finset.prod_congr rfl fun k _ => ?_
  have e : (((R.t : ℝ) - 1) / 2 - k + s) = ((R.t : ℝ) - 1) / 2 + s + (-(k : ℝ)) := by ring
  change galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
    (((R.t : ℝ) - 1) / 2 - k + s)) = _
  rw [e, galPol_character_block N A i hw hB hσ, iota_chi_at_frobenius N A i hw.2.1 hB hσ k.isLt,
    Complex.ofReal_neg]

/-- The half-weight shift of the cuspidal factor and that of its
rank-one twist add to the weight of the full point representation. -/
theorem galPol_normalized_twist {w : PlE H} (π : A.CG R.r) (hu : A.unr (A.locG π w)) (u : ℂ)
    (hξ : A.frobEig (A.lpTw (A.locG A.etaTinv w) (-(R.t : ℝ) / 2)) = {u}) :
    galPol A (A.lpTw (A.locG (A.tw π A.etaTinv) w) ((1 - (R.nV : ℝ)) / 2)) =
      (((A.frobEig (A.lpTw (A.locG π w) ((1 - (R.r : ℝ)) / 2))).map (· * u)).map fun α => X - C α).prod := by
  obtain ⟨h1, -⟩ := A.etaTinv_def w
  have d1 := A.locG_dim A.etaTinv w
  obtain ⟨d, hd⟩ := Multiset.card_eq_one.mp ((A.frobEig_card _ h1).trans d1)
  rw [A.frobEig_tw _ _ h1, hd, Multiset.map_singleton, Multiset.singleton_inj] at hξ
  unfold galPol
  rw [A.locG_tw, A.frobEig_tw _ _ (A.unr_char _ _ d1 hu h1), A.frobEig_char _ _ d hu h1 d1 hd,
    A.frobEig_tw _ _ hu]
  simp only [Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun α _ => ?_)
  simp only [Function.comp]
  rw [← hξ]
  have hq0 : (normV w : ℂ) ≠ 0 := by
    have : Finite (𝓞 H.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hq : ((normV w : ℕ) : ℂ) ^ (((1 - (R.nV : ℝ)) / 2 : ℝ) : ℂ) =
      ((normV w : ℕ) : ℂ) ^ (((1 - (R.r : ℝ)) / 2 : ℝ) : ℂ) *
        ((normV w : ℕ) : ℂ) ^ ((-(R.t : ℝ) / 2 : ℝ) : ℂ) := by
    rw [← Complex.cpow_add _ _ hq0]
    congr 1
    rw [Ranks.nV]
    push_cast
    ring
  rw [hq]
  congr 2
  ring

end WindowedLandauTheory.NormalizedTypes
