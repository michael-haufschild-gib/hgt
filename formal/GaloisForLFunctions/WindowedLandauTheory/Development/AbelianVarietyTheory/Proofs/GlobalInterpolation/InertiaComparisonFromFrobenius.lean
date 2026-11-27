import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.TwGood
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuityOfCoefficientEmbedding
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.Topology.Algebra.MvPolynomial

/-! Away from the coefficient characteristic, the local parameter of a
Galois representation reads the inertia polynomial of any integral model
with matching Frobenius polynomials on the cofinite split places. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open WindowedLandauTheory.MainNotions WindowedLandauTheory.MainNotions.N ReciprocityTheory.Gal

namespace WindowedLandauTheory.NormalizedTypes

private theorem continuous_charpoly_coeff {K : Type} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (n j : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff j := by
  have he : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff j) = fun M =>
      MvPolynomial.eval (fun p : Fin n × Fin n => M p.1 p.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff j) := funext fun M =>
    (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K)
      (fun p : Fin n × Fin n => M p.1 p.2) j).symm
  rw [he]
  exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)

theorem charpoly_eq_of_dense {Γ K : Type} [TopologicalSpace Γ] [CommRing K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] {n : ℕ}
    {a b : Γ → Matrix (Fin n) (Fin n) K} {S : Set Γ}
    (hS : Dense S) (ha : Continuous a) (hb : Continuous b)
    (he : ∀ s ∈ S, (a s).charpoly = (b s).charpoly) (s : Γ) :
    (a s).charpoly = (b s).charpoly := by
  ext j
  exact congrFun (Continuous.ext_on hS ((continuous_charpoly_coeff n j).comp ha)
    ((continuous_charpoly_coeff n j).comp hb) (fun z hz => congrArg (coeff · j) (he z hz))) s

/-- Frobenius elements at split places remain dense after discarding any
finite set of places. -/
def SplitFrobeniusDense (D : D7) : Prop :=
  ∀ T : Set (PlE D.host), T.Finite → Dense {s : D.nd.Om ≃ₐ[D.host.E] D.nd.Om |
    ∃ w : PlE D.host, w ∉ T ∧ IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
      IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) s}

variable {D : D7} (i : D.nd.Loc)
local notation "Γ" => (D.nd.Om ≃ₐ[D.host.E] D.nd.Om)
local notation "ℓ" => D.nd.l i

/-- Agreement on cofinite split Frobenius elements determines the integral
model's characteristic polynomial on the whole Galois group. -/
theorem charpoly_eq_of_cofinite_split_frobenius
    (ρ : Γ →* GL (Fin D.R.r) (D.nd.O i)) (hρ : Continuous fun g => (ρ g).val)
    (r : Γ →* GL (Fin D.R.r) (PadicAlgCl ℓ)) (hr : Continuous fun g => (r g).val)
    (hF : SplitFrobeniusDense D)
    (h : ∀ᶠ v in Filter.cofinite, IsSplitPl D.host v →
      ∀ (B : ValuationSubring D.nd.Om) (g : Γ), IsPlaceOver (F := D.host.E) B v →
        IsFrob (F := D.host.E) B (normV v) g →
        (ρ g).val.charpoly.map (iotaO D.nd D.naut i) =
          (r g).val.charpoly.map (D.naut.iotaQC i).toRingHom)
    (s : Γ) :
    ((ρ s).val.map (iotaOQ D.nd D.naut i)).charpoly = (r s).val.charpoly := by
  let j := iotaOQ D.nd D.naut i
  let e := (D.naut.iotaQC i).toRingHom
  have hmap : e.comp j = iotaO D.nd D.naut i := rfl
  have hd := hF _ (Filter.eventually_cofinite.mp h)
  have hc : Continuous fun u => (ρ u).val.map j := hρ.matrix_map (continuous_iotaOQ D i)
  refine charpoly_eq_of_dense hd hc hr (fun u hu => ?_) s
  obtain ⟨v, hv, hsplit, B, hB, hφ⟩ := hu
  apply Polynomial.map_injective e e.injective
  rw [Matrix.charpoly_map, Polynomial.map_map, hmap]
  exact (not_not.mp hv) hsplit B u hB hφ

/-- Frobenius matching compares the integral and p-adic representations on
the entire absolute Galois group before the inertia comparison is read. -/
theorem inertia_charpoly_of_frobenius {P : List (Part D.naut.CG)}
    {ρ : Γ →* GL (Fin D.R.r) (D.nd.O i)} (hρ : IsRepOfSig D.nd D.naut i P ρ)
    (r : Γ →* GL (Fin D.R.r) (PadicAlgCl ℓ)) (hr : Continuous fun s => (r s).val)
    (hU : ∀ᶠ w in Filter.cofinite, D.naut.unr (isoLoc D.nd D.naut P w))
    (hW : ∀ w, w ∉ placesOver D.host.E ℓ → D.naut.unr (isoLoc D.nd D.naut P w) →
      D.naut.wdOf i r w = D.naut.lpTw (isoLoc D.nd D.naut P w) ((1 - (D.R.r : ℝ)) / 2))
    (hF : SplitFrobeniusDense D)
    (w : PlE D.host) (hw : w ∉ placesOver D.host.E ℓ)
    (s : Γ) (hs : s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w))
    (hI : D.naut.inePol (D.naut.wdOf i r w) s =
      D.naut.inePol (D.naut.lpTw (isoLoc D.nd D.naut P w) ((1 - (D.R.r : ℝ)) / 2)) s) :
    (ρ s).val.charpoly.map (iotaO D.nd D.naut i) = D.naut.inePol (isoLoc D.nd D.naut P w) s := by
  let j := iotaOQ D.nd D.naut i
  let e := (D.naut.iotaQC i).toRingHom
  have hmap : e.comp j = iotaO D.nd D.naut i := rfl
  have hfinite := MainNotions.placesOver_finite_av D.host.E ℓ (D.nd.lPrime i).out.ne_zero
  have hcmp : ∀ᶠ v in Filter.cofinite, IsSplitPl D.host v →
      ∀ (B : ValuationSubring D.nd.Om) (g : Γ), IsPlaceOver (F := D.host.E) B v →
        IsFrob (F := D.host.E) B (normV v) g →
        (ρ g).val.charpoly.map (iotaO D.nd D.naut i) = (r g).val.charpoly.map e := by
    filter_upwards [hfinite.eventually_cofinite_notMem, hU, hρ.2.2] with v hv hu hρv _ B g hB hφ
    have hwd := hW v hv hu
    have hUnr : D.naut.unr (D.naut.wdOf i r v) := by
      rw [hwd, D.naut.unr_tw]
      exact hu
    rw [hρv B g hB hφ, D.naut.wdOf_frob i r v hv hr hUnr B g hB hφ, hwd]
    rfl
  have hchar := charpoly_eq_of_cofinite_split_frobenius i ρ hρ.1 r hr hF hcmp s
  rw [← hmap, ← Polynomial.map_map, ← Matrix.charpoly_map, hchar, D.naut.wdOf_ine i r w hw hr s hs,
    hI, D.naut.inePol_tw _ _ _ hs]

end WindowedLandauTheory.NormalizedTypes
