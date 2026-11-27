import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-! Before local rows are attached, unramified parameters are multisets of
nonzero Frobenius eigenvalues. Direct sum and twisting give the local operations. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions
open WindowedLandauTheory.ConjugateSelfDual

namespace GlobalTheory.EmptyLocalStage

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

private abbrev UnrPar : Type := {m : Multiset ℂ // (0 : ℂ) ∉ m}

def UnrPar.scale (a : UnrPar) (c : ℂ) (hc : c ≠ 0) : UnrPar :=
  ⟨a.1.map (· * c), fun h => by
    obtain ⟨x, hx, h0⟩ := Multiset.mem_map.1 h
    exact a.2 ((mul_eq_zero.1 h0).resolve_right hc ▸ hx)⟩

def UnrPar.add (a b : UnrPar) : UnrPar :=
  ⟨a.1 + b.1, fun h => (Multiset.mem_add.1 h).elim a.2 b.2⟩

private theorem normV_cpow_ne_zero (w : PlE H) (s : ℂ) : ((normV w : ℕ) : ℂ) ^ s ≠ 0 := by
  have : Finite (𝓞 H.E ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  have h : normV w ≠ 0 := Nat.card_pos.ne'
  exact fun h0 => h (by exact_mod_cast ((Complex.cpow_eq_zero_iff _ _).1 h0).1)

private theorem normV_ne_zero (w : PlE H) : ((normV w : ℕ) : ℂ) ≠ 0 := by
  simpa using normV_cpow_ne_zero w 1

private abbrev UnrFam (H : Host R) (a : ℕ) : Type :=
  {p : (PlE H → UnrPar) × ((H.E →+* ℂ) → Multiset ℂ) //
    (∀ w, Multiset.card (p.1 w).1 = a) ∧ ∀ τ, Multiset.card (p.2 τ) = a}

private def negOneFam (H : Host R) : UnrFam H 1 :=
  ⟨(fun _ => ⟨{-1}, by simp⟩, fun _ => {0}), fun _ => rfl, fun _ => rfl⟩


/-- An empty local stage has an unramified parameter model with its specified auxiliary places. -/
def unramifiedNAut (N : NData R H what₂) [IsEmpty N.Loc] (pl : ∀ k, N.PlG k → PlE H)
    (h1 : ∀ k v, pl k v ∈ placesOver H.E (H.g k)) (h2 : ∀ k, Function.Injective (pl k))
    (h3 : ∀ k v v', ¬ IsConjPl H (pl k v) (pl k v')) : NAut N where
  LP := fun _ => UnrPar
  lpDim := fun a => Multiset.card a.1
  lpZero := fun _ => ⟨0, by simp⟩
  lpSum := UnrPar.add
  lpTw := fun {w} a s => a.scale (((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) (normV_cpow_ne_zero w _)
  lpChar := fun a χ => a.scale χ.1.prod (Multiset.prod_ne_zero χ.2)
  lpUnr := fun _ m => open Classical in ⟨m.filter (· ≠ 0), by simp⟩
  mono0 := fun _ => True
  unr := fun _ => True
  frobEig := fun a => a.1
  tempered := fun a => ∀ α ∈ a.1, ‖α‖ = 1
  inePol := fun a _ => (X - 1) ^ Multiset.card a.1
  items₂ := fun _ _ a => (X - 1) ^ Multiset.card a.1
  lpDim_zero := fun _ => rfl
  lpDim_sum := fun a b => Multiset.card_add _ _
  lpDim_tw := fun a s => Multiset.card_map _ _
  lpUnr_spec := fun _ m hm => by
    classical
    have h : m.filter (· ≠ 0) = m := Multiset.filter_eq_self.2 fun x hx h0 => hm (h0 ▸ hx)
    exact ⟨trivial, h, congrArg Multiset.card h⟩
  unr_sum := fun _ _ => by simp
  monomial_sum_iff := fun _ _ => by simp
  frobEig_sum := fun _ _ _ _ => rfl
  unr_tw := fun _ _ => Iff.rfl
  monomial_twist_iff := fun _ _ => Iff.rfl
  frobEig_tw := fun _ _ _ => rfl
  frobEig_char := fun a χ c _ _ _ h => by
    show a.1.map (· * χ.1.prod) = _
    rw [show χ.1 = {c} from h, Multiset.prod_singleton]
  lpDim_char := fun _ _ _ => Multiset.card_map _ _
  unr_char := fun _ _ _ _ _ => trivial
  monomial_char_iff := fun _ _ _ => Iff.rfl
  lpZero_unr := fun _ => trivial
  frobEig_zero := fun _ => rfl
  lpSum_zero := fun a => Subtype.ext (add_zero a.1)
  lpSum_comm := fun a b => Subtype.ext (add_comm a.1 b.1)
  lpSum_assoc := fun a b c => Subtype.ext (add_assoc a.1 b.1 c.1)
  lpTw_zero := fun a => Subtype.ext (by simp [UnrPar.scale])
  lpTw_add := fun {w} a s t => Subtype.ext (by
    simp [UnrPar.scale, Complex.cpow_add _ _ (normV_ne_zero w), mul_assoc])
  lpTw_sum := fun a b s => Subtype.ext (Multiset.map_add _ _ _)
  unr_eq_lpUnr := fun a _ => by
    classical
    have h : a.1.filter (· ≠ 0) = a.1 := Multiset.filter_eq_self.2 fun x hx h0 => a.2 (h0 ▸ hx)
    exact Subtype.ext h.symm
  unr_mono0 := fun _ _ => trivial
  frobEig_ne_zero := fun a _ => a.2
  frobEig_card := fun _ _ => rfl
  tempered_unr := fun _ _ => Iff.rfl
  inePol_sum := fun a b _ => by
    show (X - 1 : ℂ[X]) ^ Multiset.card (a.1 + b.1) = _
    rw [Multiset.card_add, pow_add]
  inePol_tw := fun a s _ _ => by
    show (X - 1 : ℂ[X]) ^ Multiset.card (a.1.map _) = _
    rw [Multiset.card_map]
  unr_iff_ine := fun _ => ⟨fun _ => ⟨trivial, fun _ _ => rfl⟩, fun _ => trivial⟩
  inertiaCharpoly_zero := fun _ _ => pow_zero _
  inertiaCharpoly_add := fun k _ a b => by
    show (X - 1 : (ZMod (H.g k))[X]) ^ Multiset.card (a.1 + b.1) = _
    rw [Multiset.card_add, pow_add]
  CG := UnrFam H
  csd := fun π => ∀ w w', IsConjPl H w w' → (π.1.1 w').1 = (π.1.1 w).1.map (·⁻¹)
  ralg := fun {a} π => ∀ τ, (π.1.2 τ).Nodup ∧ ∀ z ∈ π.1.2 τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
  locG := fun π w => π.1.1 w
  locG_dim := fun π w => π.2.1 w
  locG_unr_ae := fun _ => Filter.Eventually.of_forall fun _ => trivial
  tw := fun π χ => ⟨(fun w => (π.1.1 w).scale (χ.1.1 w).1.prod (Multiset.prod_ne_zero (χ.1.1 w).2),
    fun τ => (π.1.2 τ).map (· + (χ.1.2 τ).sum)), fun w => (Multiset.card_map _ _).trans (π.2.1 w),
    fun τ => (Multiset.card_map _ _).trans (π.2.2 τ)⟩
  locG_tw := fun _ _ _ => rfl
  infG := fun π τ => π.1.2 τ
  infG_card := fun π τ => π.2.2 τ
  ralg_def := fun _ => Iff.rfl
  infG_tw := fun π χ τ s h => by
    show (π.1.2 τ).map (· + (χ.1.2 τ).sum) = _
    rw [show χ.1.2 τ = {s} from h, Multiset.sum_singleton]
  csd_tw := fun π χ hχ hπ w w' h => by
    show (π.1.1 w').1.map (· * (χ.1.1 w').1.prod) = ((π.1.1 w).1.map (· * (χ.1.1 w).1.prod)).map (·⁻¹)
    rw [hχ w w' h, hπ w w' h, Multiset.prod_map_inv', Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun x _ => (mul_inv _ _).symm
  csd_unr := fun π w w' h hc _ => ⟨trivial, h w w' hc⟩
  etaT := negOneFam H
  etaTinv := negOneFam H
  etaT_unr := fun _ => trivial
  etaT_inert := fun _ _ => rfl
  etaTinv_def := fun _ => ⟨trivial, by simp [negOneFam]⟩
  etaT_split := fun _ _ _ _ a b ha hb => by
    have ha' : (-1 : ℂ) = a := Multiset.singleton_inj.1 ha
    have hb' : (-1 : ℂ) = b := Multiset.singleton_inj.1 hb
    rw [← ha', ← hb']
    norm_num
  plGw := pl
  plGw_over := h1
  plGw_inj := h2
  plGw_nconj := h3
  iotaQ := fun i => isEmptyElim i
  iotaQC := fun i => isEmptyElim i
  iota_LL := fun i => isEmptyElim i
  iotaQ_alg := fun i => isEmptyElim i
  muC := fun i => isEmptyElim i
  muC_csd := fun i => isEmptyElim i
  AV := fun i => isEmptyElim i
  finAV := fun i => isEmptyElim i
  ptV := fun i => isEmptyElim i
  typeV := fun i => isEmptyElim i
  typeV_ne := fun i => isEmptyElim i
  typeV_indep := fun i => isEmptyElim i
  typeV_top := fun i => isEmptyElim i
  pt_surj := fun i => isEmptyElim i
  eig_dim := fun i => isEmptyElim i
  locV := fun i => isEmptyElim i
  satV := fun i => isEmptyElim i
  locV_unr := fun i => isEmptyElim i
  pt_loc := fun i => isEmptyElim i
  infWt := fun i => isEmptyElim i
  locW := fun i => isEmptyElim i
  satW := fun i => isEmptyElim i
  lab_loc := fun i => isEmptyElim i
  wdOf := fun i => isEmptyElim i
  wdOf_dim := fun i => isEmptyElim i
  wdOf_unr := fun i => isEmptyElim i
  wdOf_frob := fun i => isEmptyElim i
  wdOf_ine := fun i => isEmptyElim i
  wdOf_mono0 := fun i => isEmptyElim i
  IsCrysW := fun i => isEmptyElim i
  IsPotCrysW := fun i => isEmptyElim i
  IsdRW := fun i => isEmptyElim i
  jumpsW := fun i => isEmptyElim i
  wdOf_unrL := fun i => isEmptyElim i
  wdOf_mono0L := fun i => isEmptyElim i
  jumpsInf := fun i => isEmptyElim i
  locAutHodgeTateWeightsLevelZero := fun i => isEmptyElim i
  jumpsInf_def := fun i => isEmptyElim i
  locAut_hodgeTateWeightsLevelZero_def := fun i => isEmptyElim i
  chi_mu := fun i => isEmptyElim i
  kFbar := fun i => isEmptyElim i

/-- There are no base-change eigenspaces to realize at an empty local stage. -/
def emptyNBC {N : NData R H what₂} [IsEmpty N.Loc] (A : NAut N) : NBC A where
  AU := fun _ => Empty
  multAU := fun _ x => x.elim
  sphAU := fun _ x => x.elim
  locAU := fun _ x => x.elim
  satAU := fun _ x => x.elim
  satAU_card := fun _ x => x.elim
  Wt := fun _ => Empty
  infW := fun _ x => x.elim
  infW_card := fun _ x => x.elim
  wtAU := fun _ x => x.elim
  infW_alg := fun _ x => x.elim
  embAV := fun i => isEmptyElim i
  embAV_inj := fun i => isEmptyElim i
  embAV_loc := fun i => isEmptyElim i
  embAV_sat := fun i => isEmptyElim i
  embAV_sph := fun i => isEmptyElim i
  embAV_inf := fun i => isEmptyElim i

end GlobalTheory.EmptyLocalStage
