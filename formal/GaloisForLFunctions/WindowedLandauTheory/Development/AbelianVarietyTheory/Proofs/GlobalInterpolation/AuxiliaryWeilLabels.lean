import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.PlacedTameLabels
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitPlaceOrder

/-! Auxiliary primes split completely in the host, so each designated
place has a prime residue cardinality. The normalized tame generator
and Teichmüller lift give its Weil–Deligne label. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.ConjugateSelfDual
open ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.TameKummer
open WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.NormalizedTypes

variable {D : D7} {jE : D.host.E →+* AlgebraicClosure ℚ}
variable (T : NormalizedTypesCompatibility D jE)
variable (k : Fin 2) (v : D.nd.PlG k)

local notation "w" => (D.naut.plGw k v)
local notation "A" => (Subtype.val D.nd.plOm (D.naut.plGw k v))
local notation "h" => (Subtype.property D.nd.plOm (D.naut.plGw k v))
local notation "Γ" => (D.nd.Om ≃ₐ[D.host.E] D.nd.Om)
local notation "p" => (D.host.g k)

private theorem auxiliary_valuation_lt_one : (A).valuation (p : D.nd.Om) < 1 := by
  simpa using (h (p : 𝓞 D.host.E)).mpr (D.naut.plGw_over k v)

private theorem normV_auxiliary : normV w = p :=
  (normV_and_notMem_sq_of_split (D.host.g_prime k) (D.nd.g_split k) w (D.naut.plGw_over k v)).1

private def auxiliaryTameElement : Ine (F := D.host.E) A :=
  ⟨D.ntypes.tg k v, D.ntypes.tg_mem k v⟩

/-- The canonical polynomial read from the tame inertia of the local parameter. -/
def auxiliaryWeilLabel (x : WD h) : (ZMod p)[X] :=
  haveI : Fact (p).Prime := ⟨D.host.g_prime k⟩
  WD.tameLabel (auxiliary_valuation_lt_one k v) (normV_auxiliary k v)
    (T.teichC_def k) (auxiliaryTameElement k v) x

theorem auxiliaryWeilLabel_monic (x : WD h) : (auxiliaryWeilLabel T k v x).Monic := by
  letI : Fact (p).Prime := ⟨D.host.g_prime k⟩
  exact WD.monic_tameLabel _ _ _ _ x

theorem auxiliaryWeilLabel_degree_le (x : WD h) :
    (auxiliaryWeilLabel T k v x).natDegree ≤ x.lpDim := by
  letI : Fact (p).Prime := ⟨D.host.g_prime k⟩
  exact WD.natDegree_tameLabel_le _ _ _ _ x

theorem auxiliaryWeilLabel_sum (x y : WD h) :
    auxiliaryWeilLabel T k v (WD.lpSum x y) = auxiliaryWeilLabel T k v x * auxiliaryWeilLabel T k v y := by
  letI : Fact (p).Prime := ⟨D.host.g_prime k⟩
  exact WD.tameLabel_sum _ _ _ _ x y

theorem auxiliaryWeilLabel_unramified_twist (x : WD h) (c : ℂˣ) :
    auxiliaryWeilLabel T k v (WD.lpTwist x (unrChar h c) (isSmooth_unrChar h c)) =
      auxiliaryWeilLabel T k v x := by
  letI : Fact (p).Prime := ⟨D.host.g_prime k⟩
  exact WD.tameLabel_unramified_twist _ _ _ _ x c

theorem auxiliaryWeilLabel_tame_charpoly (x : WD h)
    (hx : (auxiliaryWeilLabel T k v x).natDegree = x.lpDim) :
    haveI : Fact (p).Prime := ⟨D.host.g_prime k⟩
    x.charpoly (ineIncl h ⟨D.ntypes.tg k v, D.ntypes.tg_mem k v⟩) =
      ((rootsBar (auxiliaryWeilLabel T k v x)).map fun z => X - C (D.ntypes.teichC k z)).prod := by
  letI : Fact (p).Prime := ⟨D.host.g_prime k⟩
  exact WD.charpoly_eq_of_full_tameLabel _ _ _ _ x hx

/-- Full degree of the local label forces wild inertia to act trivially
on the entire Weil–Deligne parameter. -/
theorem auxiliaryWeilLabel_wild_charpoly (x : WD h)
    (hx : (auxiliaryWeilLabel T k v x).natDegree = x.lpDim)
    (s : Γ) (hs : s ∈ wildInertia (E := D.host.E) A) :
    x.charpoly (ineIncl h ⟨s, wildInertia_le_inertia A hs⟩) = (X - (1 : ℂ[X])) ^ x.lpDim := by
  letI : Fact (p).Prime := ⟨D.host.g_prime k⟩
  exact WD.charpoly_wild_of_full_tameLabel _ _ _ _ x hx _ hs

end WindowedLandauTheory.NormalizedTypes
