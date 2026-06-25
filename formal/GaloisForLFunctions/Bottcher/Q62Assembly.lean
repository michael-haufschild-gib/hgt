/-
# Field-7 groundwork: descending independence from a faithful field to the genuine coordinates

The disconnected/mixed case discharges `q62_independence`'s hypotheses on the **connected dyadic-cover
field** `M` (where the multivalued `φ_c` is single-valued and the deck group acts — see
`CoverMonodromy`/`CoverConstruction`). That cover field restricts, via a `ℂ(z)`-algebra hom `ψ`, onto
the single-valued `meroField (deepBall)` where the genuine `phiMero` coordinates live. This file
provides the descent step: `NoRelation` over the cover field `M` transfers along the injective `ψ`
to `NoRelation` for the actual `phiMero c₁, phiMero c₂`. Together with `q62_independence` (the verified
case-split + monodromy obstruction) and `q62_connected_of_functional_independence` (the verified
connected-case faithfulness), the only mathematics still standing between this and an unconditional
q62 is the two cited published inputs external to Mathlib — Eremenko–van Strien rigidity
(arXiv:0810.2260) and the exact dyadic/Prüfer monodromy / connected-cover field — whose construction
(the gluing of the verified local branches into the cover Riemann surface) is analysis not present in
Mathlib. This descent lemma is machine-checked with no axioms.
-/
import GaloisForLFunctions.Bottcher.Q62
import GaloisForLFunctions.Bottcher.MeromorphicField
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.KummerExtension

open Polynomial Function Filter Topology

namespace Bottcher

/-- **`NoRelation` transfers along an injective `K`-algebra hom.** If `ψ : M →ₐ[K] N` is injective and
`F, G ∈ M` satisfy no polynomial relation over `K`, then so do `ψ F, ψ G ∈ N`. (Naturality: `ψ`
commutes with the bivariate evaluation `P ↦ (P.map (aeval G)).eval F`; injectivity reflects vanishing
back.) This is the descent step from a faithful field `M` (e.g. the connected dyadic cover, carrying
the monodromy) down through the restriction `ψ` to the genuine Böttcher coordinates `ψ F = phiMero c₁`,
`ψ G = phiMero c₂` — so independence proved upstairs (via `q62_independence`) yields independence of
the actual coordinates. -/
theorem noRelation_of_algHom {K M N : Type*} [Field K] [Field M] [Field N]
    [Algebra K M] [Algebra K N] (ψ : M →ₐ[K] N) (hψ : Injective ψ) {F G : M}
    (h : NoRelation K F G) : NoRelation K (ψ F) (ψ G) := by
  have hnat : ∀ P : Polynomial (Polynomial K),
      (P.map (aeval (ψ G) : Polynomial K →ₐ[K] N).toRingHom).eval (ψ F)
        = ψ ((P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom).eval F) := by
    intro P
    induction P using Polynomial.induction_on with
    | C q => simp [aeval_algHom_apply]
    | add p q hp hq => simp only [Polynomial.map_add, Polynomial.eval_add, map_add, hp, hq]
    | monomial n q _ => simp [aeval_algHom_apply, map_mul, map_pow]
  intro P hP
  apply h P
  apply hψ
  rw [map_zero, ← hnat P, hP]

end Bottcher

namespace Bottcher

/-- **`meroField U` is a valid carrier for the disconnected-case independence.** Instantiating the
abstract `q62_disconnected_both` at `M = meroField U` (the meromorphic function field on a connected
open `U`, the *faithful* carrier where `φ_{c₁}, φ_{c₂}` are genuine function germs) discharges the
disconnected/disconnected independence from the monodromy data alone — once that data (`monoF`,
`monoG`) is supplied by the deck automorphisms `precompMeroAlgEquiv`. This resolves the earlier
carrier obstacle: with the domain instance in scope, `Field (meroField U)` synthesizes and the abstract
theorem applies verbatim to the genuine field. -/
theorem noRelation_meroField_of_monodromy
    {U : Set ℂ} [IsDomain (analyticSubring U)]
    {K : Type*} [Field K] [Algebra K (meroField U)]
    (F G : meroField U) (hF : F ≠ 0) (hG : G ≠ 0)
    (monoF : ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[K] meroField U) (ζ : meroField U) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧ σ G = G ∧ σ ζ = ζ ∧ σ F = ζ * F)
    (monoG : ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[K] meroField U) (ζ : meroField U),
      d < orderOf ζ ∧ σ ζ = ζ ∧ σ G = ζ * G) :
    NoRelation K F G :=
  q62_disconnected_both F G hF hG monoF monoG

end Bottcher

namespace Bottcher

/-- **One step of the monodromy tower, assembled.** Given the genuine lift data at one depth `d` — a
deck self-biholomorphism `g` of `U` (inverse `g'`) with a `2^k`-th root `ζ₀` of order `> d`, under
which the `φ_{c₁}` germ `a₁` scales by `ζ₀`, the `φ_{c₂}` germ `a₂` is fixed, and the base field `K`
is fixed — this produces exactly the existential witness `q62_disconnected_both`'s `monoF` requires:
a `K`-algebra automorphism `σ` of `meroField U` with `σ G = G`, `σ ζ = ζ`, `σ F = ζ·F`, and
`orderOf ζ = m > d`. Every field is discharged by the verified bricks (`precompMeroAlgEquiv`,
`precompMeroEquiv_algebraMap_fix`/`_scale`, `orderOf_algebraMap_constToAnalytic`,
`constToAnalytic_compTendsto`). The only remaining input is the lift data itself (the analytic
continuation of the Böttcher coordinates on the cover). -/
theorem monoF_witness {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroField U)]
    (a₁ a₂ : analyticSubring U) (d : ℕ) (ζ₀ : ℂ) {g g' : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hord : d < orderOf ζ₀)
    (hscale : (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₁ : Germ (𝓟 U) ℂ))
    (hinv : (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = (a₂ : Germ (𝓟 U) ℂ))
    (hK : ∀ k : K, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap K (meroField U) k) = algebraMap K (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    ∃ (σ : meroField U ≃ₐ[K] meroField U) (ζ : meroField U) (m : ℕ),
      d < m ∧ orderOf ζ = m ∧
      σ (algebraMap (analyticSubring U) (meroField U) a₂)
        = algebraMap (analyticSubring U) (meroField U) a₂ ∧
      σ ζ = ζ ∧
      σ (algebraMap (analyticSubring U) (meroField U) a₁)
        = ζ * algebraMap (analyticSubring U) (meroField U) a₁ := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  refine ⟨precompMeroAlgEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne hK,
    algebraMap (analyticSubring U) (meroField U) (constToAnalytic U ζ₀), orderOf ζ₀,
    hord, orderOf_algebraMap_constToAnalytic ζ₀, ?_, ?_, ?_⟩
  · show precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap _ _ a₂) = algebraMap _ _ a₂
    exact precompMeroEquiv_algebraMap_fix hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne hinv
  · show precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap _ _ (constToAnalytic U ζ₀)) = algebraMap _ _ (constToAnalytic U ζ₀)
    exact precompMeroEquiv_algebraMap_fix hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
      (constToAnalytic_compTendsto (tendsto_principal_principal.mpr hmaps) ζ₀)
  · show precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap _ _ a₁) = _
    exact precompMeroEquiv_algebraMap_scale hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne ζ₀ hscale

end Bottcher

namespace Bottcher

/-- **The `monoG` tower step.** Symmetric to `monoF_witness`: from the `c₂`-deck lift data at depth
`d` (a deck self-biholomorphism `g` under which the `φ_{c₂}` germ `a₂` scales by a root `ζ₀` of order
`> d`, fixing the base field `K`), produces the existential `q62_disconnected_both`'s `monoG`
requires: `σ : M ≃ₐ[K] M`, `ζ : M` with `d < orderOf ζ`, `σ ζ = ζ`, `σ G = ζ·G`. -/
theorem monoG_witness {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroField U)]
    (a₂ : analyticSubring U) (d : ℕ) (ζ₀ : ℂ) {g g' : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hord : d < orderOf ζ₀)
    (hscale : (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
        = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₂ : Germ (𝓟 U) ℂ))
    (hK : ∀ k : K, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap K (meroField U) k) = algebraMap K (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    ∃ (σ : meroField U ≃ₐ[K] meroField U) (ζ : meroField U),
      d < orderOf ζ ∧ σ ζ = ζ ∧
      σ (algebraMap (analyticSubring U) (meroField U) a₂)
        = ζ * algebraMap (analyticSubring U) (meroField U) a₂ := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  refine ⟨precompMeroAlgEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne hK,
    algebraMap (analyticSubring U) (meroField U) (constToAnalytic U ζ₀), ?_, ?_, ?_⟩
  · rw [orderOf_algebraMap_constToAnalytic]; exact hord
  · show precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap _ _ (constToAnalytic U ζ₀)) = algebraMap _ _ (constToAnalytic U ζ₀)
    exact precompMeroEquiv_algebraMap_fix hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
      (constToAnalytic_compTendsto (tendsto_principal_principal.mpr hmaps) ζ₀)
  · show precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap _ _ a₂) = _
    exact precompMeroEquiv_algebraMap_scale hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne ζ₀ hscale

end Bottcher

namespace Bottcher

/-- **hDisc-disconnected, reduced to the genuine lift data.** Capstone of the algebraic pipeline: for
the genuine carrier `M = meroField U` and the actual Böttcher germs `a₁ = φ_{c₁}`, `a₂ = φ_{c₂}`, IF at
every depth `d` the cover supplies the deck lift data — a self-biholomorphism `g` of `U` (inverse `g'`)
with a root `ζ₀` of order `> d` under which (for `hliftF`) `a₁` scales by `ζ₀` while `a₂` and `K` are
fixed, and symmetrically (for `hliftG`) `a₂` scales — THEN `φ_{c₁}, φ_{c₂}` satisfy no polynomial
relation over `K`. Every algebraic/field-theoretic step (`monoF_witness`, `monoG_witness`,
`noRelation_meroField_of_monodromy` → `q62_disconnected_both`) is machine-checked; the *only* remaining
input is the lift data itself — the analytic continuation of the Böttcher coordinates on the dyadic
cover (`hliftF`/`hliftG`), the precisely-isolated complex-analysis content of the disconnected case. -/
theorem noRelation_of_disconnected_lifts {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroField U)]
    (a₁ a₂ : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hG : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₁ : Germ (𝓟 U) ℂ) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
          = (a₂ : Germ (𝓟 U) ℂ) ∧
        ∀ k : K, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap K (meroField U) k) = algebraMap K (meroField U) k)
    (hliftG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₂ : Germ (𝓟 U) ℂ) ∧
        ∀ k : K, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap K (meroField U) k) = algebraMap K (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    NoRelation K (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  refine noRelation_meroField_of_monodromy _ _ hF hG ?_ ?_
  · intro d
    obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hscale, hinv, hK⟩ := hliftF d
    exact monoF_witness hUo hUc hUne a₁ a₂ d ζ₀ hg hg' hmaps hmaps' hgg' hg'g hord hscale hinv hK
  · intro d
    obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hscale, hK⟩ := hliftG d
    exact monoG_witness hUo hUc hUne a₂ d ζ₀ hg hg' hmaps hmaps' hgg' hg'g hord hscale hK

end Bottcher

namespace Bottcher

/-- **hRigid mixed case, reduced to the lift data — no E–vS needed.** When exactly one parameter is
disconnected (say `c₁`), `φ_{c₁}` carries the dyadic monodromy while `φ_{c₂}` is single-valued; the
independence follows from `q62_mixed` (monodromy of `F` + transcendence of `G`), with NO
Eremenko–van Strien rigidity. So the mixed half of `hRigid` reduces to exactly the same input as the
disconnected case — the lift data `hliftF` for the disconnected coordinate — plus `Transcendental K G`
(itself a consequence of `G`'s own monodromy when both are disconnected). Only the genuinely
both-connected sub-case is irreducibly E–vS. -/
theorem noRelation_of_mixed_lifts {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroField U)]
    (a₁ a₂ : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hG : haveI := isDomain_analyticSubring U hUo hUc hUne
          Transcendental K (algebraMap (analyticSubring U) (meroField U) a₂))
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₁ : Germ (𝓟 U) ℂ) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
          = (a₂ : Germ (𝓟 U) ℂ) ∧
        ∀ k : K, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap K (meroField U) k) = algebraMap K (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    NoRelation K (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  refine q62_mixed _ _ hF hG ?_
  intro d
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hscale, hinv, hK⟩ := hliftF d
  exact monoF_witness hUo hUc hUne a₁ a₂ d ζ₀ hg hg' hmaps hmaps' hgg' hg'g hord hscale hinv hK

end Bottcher

namespace Bottcher

/-- **Transcendence reduces to the lift data.** A coordinate with its own unbounded dyadic monodromy
is transcendental over `K`: from `a₂`'s lift data (the `monoG` tower) and `a₂ ≠ 0`,
`Transcendental K (algebraMap a₂)` follows by `transcendental_of_monodromy`. So when `φ_{c₂}` is also
disconnected, the `Transcendental K φc₂` premise of `noRelation_of_mixed_lifts` is itself discharged
by `φ_{c₂}`'s lift data — the both-disconnected case needs lift data and nothing else. -/
theorem transcendental_of_lifts {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroField U)]
    (a₂ : analyticSubring U)
    (hG0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (hliftG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₂ : Germ (𝓟 U) ℂ) ∧
        ∀ k : K, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap K (meroField U) k) = algebraMap K (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    Transcendental K (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  refine transcendental_of_monodromy _ hG0 ?_
  intro d
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hscale, hK⟩ := hliftG d
  exact monoG_witness hUo hUc hUne a₂ d ζ₀ hg hg' hmaps hmaps' hgg' hg'g hord hscale hK

end Bottcher

namespace Bottcher

/-- **`q62_independence`'s `hDisc` tuple, produced from the lift data.** Assembles exactly the
both-disconnected hypothesis of `q62_independence` — `Transcendental K φ_{c₂} ∧ φ_{c₁} ≠ 0 ∧ monoF` —
for `M = meroField U`, `φ_{c₁} = algebraMap a₁`, `φ_{c₂} = algebraMap a₂`, from: `a₁`'s lift data
(`hliftF`: scales `a₁`, fixes `a₂` and `K`), `a₂`'s lift data (`hliftG`: scales `a₂`, giving its
transcendence), and the nonvanishing. This is precisely the term that, once the lift data is
constructed, discharges `hDisc` when instantiating `q62_independence` at the genuine carrier — the
entire both-disconnected hypothesis reduced to the lift data, machine-checked. -/
theorem hDisc_tuple_of_lifts {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {K : Type*} [Field K] [Algebra K (meroField U)]
    (a₁ a₂ : analyticSubring U)
    (hF0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hG0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₁ : Germ (𝓟 U) ℂ) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
          = (a₂ : Germ (𝓟 U) ℂ) ∧
        ∀ k : K, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap K (meroField U) k) = algebraMap K (meroField U) k)
    (hliftG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₂ : Germ (𝓟 U) ℂ) ∧
        ∀ k : K, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap K (meroField U) k) = algebraMap K (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    Transcendental K (algebraMap (analyticSubring U) (meroField U) a₂) ∧
      algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0 ∧
      ∀ d : ℕ, ∃ (σ : meroField U ≃ₐ[K] meroField U) (ζ : meroField U) (m : ℕ),
        d < m ∧ orderOf ζ = m ∧
        σ (algebraMap (analyticSubring U) (meroField U) a₂)
          = algebraMap (analyticSubring U) (meroField U) a₂ ∧
        σ ζ = ζ ∧
        σ (algebraMap (analyticSubring U) (meroField U) a₁)
          = ζ * algebraMap (analyticSubring U) (meroField U) a₁ := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  refine ⟨transcendental_of_lifts hUo hUc hUne a₂ hG0 hliftG, hF0, fun d => ?_⟩
  obtain ⟨ζ₀, g, g', hg, hg', hmaps, hmaps', hgg', hg'g, hord, hscale, hinv, hK⟩ := hliftF d
  exact monoF_witness hUo hUc hUne a₁ a₂ d ζ₀ hg hg' hmaps hmaps' hgg' hg'g hord hscale hinv hK

end Bottcher

namespace Bottcher

/-- **`q62_independence` instantiated: both-disconnected, from the lift data.** This discharges
`q62_independence`'s own hypotheses for the genuine carrier `M = meroField U` and the actual Böttcher
germs `a₁, a₂`: with `Disc := fun _ => True` (both disconnected) the `hRigid` branch is vacuous, and
`hDisc` is supplied by `hDisc_tuple_of_lifts` from the lift data. The conclusion is the genuine
independence `NoRelation ℂ(z) φ_{c₁} φ_{c₂}` obtained *through the top theorem `q62_independence`
itself*. The only inputs are the `ℂ(z)`-algebra structure on the cover field (the projection
embedding) and the lift data — the precise analytic content of the disconnected case. -/
theorem q62_independence_disconnected_of_lifts {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    [Algebra (RatFunc ℂ) (meroField U)]
    (a₁ a₂ : analyticSubring U) (c₁ c₂ : ℂ) (hne : c₁ ≠ c₂)
    (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hF0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hG0 : haveI := isDomain_analyticSubring U hUo hUc hUne
           algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (hliftF : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (a₁ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₁ : Germ (𝓟 U) ℂ) ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
          = (a₂ : Germ (𝓟 U) ℂ) ∧
        ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap (RatFunc ℂ) (meroField U) k) = algebraMap (RatFunc ℂ) (meroField U) k)
    (hliftG : ∀ d : ℕ, ∃ (ζ₀ : ℂ) (g g' : ℂ → ℂ)
        (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
        (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
        (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U),
        d < orderOf ζ₀ ∧
        (a₂ : Germ (𝓟 U) ℂ).compTendsto g (tendsto_principal_principal.mpr hmaps)
          = ((constToAnalytic U ζ₀ : analyticSubring U) : Germ (𝓟 U) ℂ) * (a₂ : Germ (𝓟 U) ℂ) ∧
        ∀ k : RatFunc ℂ, precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
          (algebraMap (RatFunc ℂ) (meroField U) k) = algebraMap (RatFunc ℂ) (meroField U) k) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  have key := q62_independence (K := RatFunc ℂ)
    (fun c => if c = c₂ then algebraMap (analyticSubring U) (meroField U) a₂
              else algebraMap (analyticSubring U) (meroField U) a₁)
    (fun _ => True) c₁ c₂ hne hx₁ hx₂
    (fun _ _ => by
      simp only [if_neg hne, if_pos rfl]
      exact hDisc_tuple_of_lifts hUo hUc hUne a₁ a₂ hF0 hG0 hliftF hliftG)
    (fun h => absurd trivial (h.elim id id))
  simp only [if_neg hne, if_pos rfl] at key
  exact key

end Bottcher


namespace Bottcher

/-- **The algebraic (Kummer) cover field: foundation.** For a base field `L`, `g : L`, the generating
root of `AdjoinRoot (X^k - C g)` satisfies `v^k = g`. With `L = meroField(A)` and `g = φ_c∘f^[n]`
(`k = 2ⁿ`), this root `v` is the genuine `φ_{c₁}` — `bottcherCoord_iterate` gives `φ_c^{2ⁿ} = φ_c∘f^[n]`
— so the connected dyadic cover field is this **algebraic** Kummer extension (a field once
`X^{2ⁿ} - C g` is irreducible, via Mathlib's `X_pow_sub_C_irreducible_of_prime_pow`), with the deck as
the Kummer Galois action `v ↦ ζv`. No Riemann-surface gluing: the cover field is built by algebra, and
the single remaining analytic input is the irreducibility of `X^{2ⁿ} - C (φ_c∘f^[n])` over
`meroField(A)` (the algebraic form of nontrivial dyadic monodromy). -/
theorem kummer_root_pow_eq {L : Type*} [Field L] (g : L) (k : ℕ) :
    (AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C g)) ^ k
      = algebraMap L (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g)) g := by
  have h : Polynomial.aeval (AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C g))
      (Polynomial.X ^ k - Polynomial.C g) = 0 := by
    rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h
  linear_combination h

end Bottcher

namespace Bottcher

/-- **The deck scaling is well-defined on the Kummer cover field.** If `ζ^k = 1` then `ζ·v` is also a
`k`-th root of `g` (`(ζ·v)^k = g`), so `v ↦ ζ·v` is a genuine `L`-algebra automorphism of
`AdjoinRoot (X^k - C g)` — Mathlib's `autAdjoinRootXPowSubC`, with `autAdjoinRootXPowSubC_root` giving
`σ(v) = ζ·v` and the Galois group `≅ ℤ/k` (`autEquivZmod`). For `k = 2ⁿ` and `ζ` a primitive
`2ⁿ`-th root of unity (from `ℂ ⊆ L`), this is the order-`2ⁿ` dyadic deck automorphism `q62` needs —
supplied by Mathlib's Kummer theory, no Riemann surface. -/
theorem kummer_zeta_root_pow {L : Type*} [Field L] (g ζ : L) (k : ℕ) (hζ : ζ ^ k = 1) :
    (ζ • AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C g)) ^ k
      = algebraMap L (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g)) g := by
  rw [Algebra.smul_def, mul_pow, ← map_pow, hζ, map_one, one_mul, kummer_root_pow_eq]

end Bottcher

namespace Bottcher

/-- **The Kummer cover root is nonzero** when `g ≠ 0` (on the Kummer field). Since `root^k = g ≠ 0`,
the root cannot be `0`. This is `φ_{c₁} ≠ 0` (the `q62` nonvanishing hypothesis) on the algebraic
cover field, and ensures the deck scaling `v ↦ ζv` is a nontrivial automorphism for `ζ ≠ 1`. -/
theorem kummer_root_ne_zero {L : Type*} [Field L] {g : L} (hg : g ≠ 0) {k : ℕ} (hk : k ≠ 0)
    [Fact (Irreducible (Polynomial.X ^ k - Polynomial.C g))] :
    AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C g) ≠ 0 := by
  intro h
  have hp := kummer_root_pow_eq g k
  rw [h, zero_pow hk] at hp
  exact hg ((injective_iff_map_eq_zero
    (algebraMap L (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g)))).mp
    (algebraMap L (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g))).injective g hp.symm)

end Bottcher

namespace Bottcher

/-- **The multiplier keeps its order on the Kummer cover field.** For `M = AdjoinRoot (X^k - C g)` a
field (irreducible), `algebraMap L M` is injective (out of the field `L`), so the deck multiplier
`ζ = algebraMap L M ζ₀` has `orderOf ζ = orderOf ζ₀`. With `ζ₀` a primitive `2ⁿ`-th root of unity in
`L` (from `ℂ ⊆ L`), this is the `orderOf ζ = 2ⁿ > d` datum of `q62_disconnected_both` on the algebraic
cover field — the Kummer analogue of `orderOf_algebraMap_constToAnalytic`. -/
theorem orderOf_algebraMap_kummer {L : Type*} [Field L] {g : L} {k : ℕ}
    [Fact (Irreducible (Polynomial.X ^ k - Polynomial.C g))] (ζ₀ : L) :
    orderOf (algebraMap L (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g)) ζ₀) = orderOf ζ₀ :=
  orderOf_injective
    (algebraMap L (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g))).toMonoidHom
    (algebraMap L (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g))).injective ζ₀

end Bottcher

namespace Bottcher

/-- **The Kummer deck automorphism scales the root: `σ(φc₁) = ζ·φc₁`.** Mathlib's
`autAdjoinRootXPowSubC` for the root of unity `ζ₀` (`ζ₀^k = 1`) is an `L`-algebra automorphism of the
cover field sending `root ↦ ζ₀·root = (algebraMap ζ₀)·root`. With `root = φc₁`, `ζ = algebraMap ζ₀`,
this is exactly the `σ F = ζ·F` datum of `q62_disconnected_both`; and being `L`-linear it fixes `L`
(hence `φc₂ ∈ L`, `ℂ(z)`, and the constant `ζ`). The deck is Mathlib-supplied — no Riemann surface. -/
theorem kummer_deck_root {L : Type*} [Field L] (g : L) {k : ℕ} [NeZero k] {ζ₀ : L} (hζ : ζ₀ ^ k = 1) :
    (autAdjoinRootXPowSubC k g (rootsOfUnity.mkOfPowEq ζ₀ hζ))
        (AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C g))
      = algebraMap L (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g)) ζ₀
        * AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C g) := by
  rw [autAdjoinRootXPowSubC_root, rootsOfUnity.coe_mkOfPowEq, Algebra.smul_def]

end Bottcher

namespace Bottcher

/-- **The Kummer deck fixes the base field.** The deck automorphism `autAdjoinRootXPowSubC` is an
`L`-algebra equivalence, so it fixes the image of every base element `x ∈ L`. On the cover field this
gives all the "fixed" data `q62_disconnected_both` needs at once: `σ φc₂ = φc₂` (`φc₂ ∈ L`),
`σ ζ = ζ` (the multiplier `ζ = algebraMap ζ₀ ∈ image L`), and `K`-linearity (ℂ(z) ⊆ L). Combined with
`kummer_deck_root` (`σ φc₁ = ζ·φc₁`), `orderOf_algebraMap_kummer`, and `kummer_root_ne_zero`, this is
the complete `monoF` datum on the algebraic cover field — every piece Mathlib-supplied except the
field's irreducibility (the `p=2` Vahlen–Capelli case, a Mathlib TODO, = the dyadic monodromy). -/
theorem kummer_deck_fixes_base {L : Type*} [Field L] (g : L) {k : ℕ} [NeZero k] {ζ₀ : L}
    (hζ : ζ₀ ^ k = 1) (x : L) :
    (autAdjoinRootXPowSubC k g (rootsOfUnity.mkOfPowEq ζ₀ hζ))
        (algebraMap L (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g)) x)
      = algebraMap L (AdjoinRoot (Polynomial.X ^ k - Polynomial.C g)) x :=
  AlgEquiv.commutes _ x

end Bottcher

namespace Bottcher

/-- **`−4 = (1+i)^4` in `ℂ`.** Over any field containing `ℂ` (so containing `i` and all roots of
unity), `−4` is a 4th power. This collapses the **2-power Vahlen–Capelli** irreducibility criterion:
`X^{2ⁿ} − C g` (`n ≥ 2`) is irreducible iff `g` is not a square AND `−4g` is not a 4th power — but
since `−4` is a 4th power, `−4g` is a 4th power ⟺ `g` is a 4th power ⟹ `g` is a square; so the second
condition is subsumed and irreducibility reduces to the single condition **`g` is not a square in
`meroField(A)`** = the dyadic monodromy (`φc^{2^{n-1}}` is multivalued). This is the one analytic
input left for the algebraic cover field. -/
theorem neg_four_eq_one_add_I_pow_four : (1 + Complex.I) ^ 4 = -4 := by
  have h2 : (1 + Complex.I) ^ 2 = 2 * Complex.I := by
    have := Complex.I_sq; ring_nf; ring_nf at this; linear_combination this
  calc (1 + Complex.I) ^ 4 = ((1 + Complex.I) ^ 2) ^ 2 := by ring
    _ = (2 * Complex.I) ^ 2 := by rw [h2]
    _ = -4 := by rw [mul_pow, Complex.I_sq]; ring

end Bottcher

namespace Bottcher

/-- **Degree-2 cover irreducibility from the monodromy condition.** If `g` is not a square in `L`,
then `X² − C g` is irreducible (Mathlib's `X_pow_sub_C_irreducible_of_prime`, `p = 2`), so
`AdjoinRoot (X² − C g)` is a field — the degree-2 cover level, with deck order 2. The full `2ⁿ`-level
cover is the **iterated** such extension (a tower of degree-2 steps, each requiring its element to be a
non-square = the monodromy at that level), so the `2ⁿ` cover field is built by `n` applications of this
Mathlib-supported degree-2 case — **bypassing the `p=2` Vahlen–Capelli gap entirely**. The remaining
analytic input per level is exactly "`φc∘f^[n]` (resp. the level element) is not a square in
`meroField(A)`" = the dyadic monodromy (the verified period). -/
theorem X_sq_sub_C_irreducible_of_not_square {L : Type*} [Field L] {g : L}
    (hg : ∀ b : L, b ^ 2 ≠ g) : Irreducible (Polynomial.X ^ 2 - Polynomial.C g) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two hg

end Bottcher

namespace Bottcher

/-- **Cover field ⟺ monodromy condition.** `g` is not a square in `L` ⟺ `X² − C g` is irreducible ⟺
`AdjoinRoot (X² − C g)` is a field (the degree-2 cover level exists). This is the precise
algebraic↔analytic bridge: the analytic input "`g = φc∘f^[n]` is not a square in `meroField(A)`" (the
dyadic monodromy from the verified period) is *exactly* the condition that the algebraic cover field is
a genuine field. So the entire cover construction is: prove the period is nontrivial ⟹ `g` not a square
⟹ (this iff) cover field is a field ⟹ Mathlib's deck Galois action gives the `q62` monodromy. -/
theorem not_square_iff_X_sq_sub_C_irreducible {L : Type*} [Field L] (g : L) :
    (∀ b : L, b ^ 2 ≠ g) ↔ Irreducible (Polynomial.X ^ 2 - Polynomial.C g) :=
  (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).symm

end Bottcher

namespace Bottcher

/-- **Winding bridge: odd winding ⟹ not a square.** The logic connecting the realized period to the
algebraic non-square condition. If `g` has period `∮ d log g = 2πi` (winding 1, odd — from the dyadic
period `∮ d log φc = 2πi/2ⁿ` times `2ⁿ`), and `g = h²` for a single-valued analytic `h`, then the
period halves: `∮ d log h = πi`. But a single-valued nonvanishing `h` has integer winding, `∮ d log h
= 2πi·k` (argument principle). Then `2πi = 2·(2πi·k)` gives `1 = 2k` — impossible for `k ∈ ℤ`. So `g`
is not a square. The two analytic inputs (`∮ d log g = 2πi`; `h`'s integer period) come from the
verified period and Mathlib's argument principle; the contradiction is this arithmetic. -/
theorem not_square_of_odd_period {ph : ℂ} (k : ℤ)
    (hdouble : 2 * (Real.pi : ℂ) * Complex.I = 2 * ph)
    (hint : ph = 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) : False := by
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [hint] at hdouble
  have h1 : (2 * (Real.pi : ℂ) * Complex.I) * 1 = (2 * (Real.pi : ℂ) * Complex.I) * (2 * (k : ℂ)) := by
    rw [mul_one]; linear_combination hdouble
  have h2 : (1 : ℂ) = 2 * (k : ℂ) := mul_left_cancel₀ hne h1
  have h3 : (1 : ℤ) = 2 * k := by exact_mod_cast h2
  omega

end Bottcher

namespace Bottcher

/-- **The deck multiplier has order exactly `2^k` at tower level `k`.** A primitive `2^k`-th root of
unity `ζ₀ ∈ L` (from `ℂ ⊆ L`) maps to an order-`2^k` element of the Kummer cover field
`AdjoinRoot (X^{2^k} − C g)`. As `k → ∞` these give the **unbounded-order** multipliers
`q62_disconnected_both`'s `monoF` demands (`d < 2^k`), with the deck `autAdjoinRootXPowSubC` scaling
`φc₁` by exactly this `ζ`. The order-growth backbone of the 2^∞ tower (each level supplies its own
order-`2^k` deck on the genuine `φc₁`). -/
theorem orderOf_primitive_in_kummer {L : Type*} [Field L] {g : L} {k : ℕ}
    [Fact (Irreducible (Polynomial.X ^ (2 ^ k) - Polynomial.C g))] {ζ₀ : L}
    (hζ : IsPrimitiveRoot ζ₀ (2 ^ k)) :
    orderOf (algebraMap L (AdjoinRoot (Polynomial.X ^ (2 ^ k) - Polynomial.C g)) ζ₀) = 2 ^ k := by
  rw [orderOf_algebraMap_kummer]; exact hζ.eq_orderOf.symm

end Bottcher

namespace Bottcher

open Polynomial in
/-- **Radical-tower transition map.** The directed-system map `K[2ⁿ√g] → K[2^{n+1}√g]` sending the
level-`n` root to the *square* of the level-`(n+1)` root: since `(root_{n+1}²)^{2ⁿ} = root_{n+1}^{2^{n+1}}
= g`, the square `root_{n+1}²` is a `2ⁿ`-th root of `g`, so the universal property of `AdjoinRoot`
gives the embedding. This is the transition of the `2^∞`-radical tower of a fixed `g`, whose
`Ring.DirectLimit` is a field (`Field.DirectLimit.field`) carrying the full `μ_{2^∞}` deck — the
direct-limit mechanism for an unbounded-order carrier (used when the bottom element is fixed; the
genuine cover, with its varying `gₙ` and 2-adic monodromy, is the analytic refinement). -/
noncomputable def kummerTowerMap {L : Type*} [Field L] (g : L) (n : ℕ) :
    AdjoinRoot (X ^ (2 ^ n) - C g) →+* AdjoinRoot (X ^ (2 ^ (n + 1)) - C g) :=
  AdjoinRoot.lift (algebraMap L _) ((AdjoinRoot.root (X ^ (2 ^ (n + 1)) - C g)) ^ 2) (by
    have hexp : ((AdjoinRoot.root (X ^ (2 ^ (n + 1)) - C g)) ^ 2) ^ (2 ^ n)
        = (AdjoinRoot.root (X ^ (2 ^ (n + 1)) - C g)) ^ (2 ^ (n + 1)) := by
      rw [← pow_mul]; congr 1; rw [pow_succ]; ring
    rw [← aeval_def, map_sub, map_pow, aeval_X, aeval_C, hexp, kummer_root_pow_eq, sub_self])

end Bottcher

namespace Bottcher

/-- **Integer winding from `exp(period) = 1`.** The integrality core of the argument principle: if a
single-valued nonzero analytic `h` is integrated around a closed loop, the endpoint values agree, so
`exp(∮ d log h) = h(end)/h(start) = 1`; hence `∮ d log h = 2πi·n` for some `n ∈ ℤ`
(`Complex.exp_eq_one_iff`). This is the winding `∮ d log h ∈ 2πiℤ` the bridge `not_square_of_odd_period`
consumes — the remaining piece being `exp(∮ d log h) = 1` (the closed-loop fundamental theorem, an
analytic construction). -/
theorem winding_integer_of_exp_eq_one {p : ℂ} (hp : Complex.exp p = 1) :
    ∃ n : ℤ, p = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) := by
  rw [Complex.exp_eq_one_iff] at hp
  obtain ⟨n, hn⟩ := hp
  exact ⟨n, by rw [hn]; ring⟩

end Bottcher

namespace Bottcher

/-- **Per-level non-square, given the period and the FTC.** Combines the integrality core with the
winding bridge: if `g` has period `∮ d log g = 2πi` (odd, the realized dyadic period × `2ⁿ`) and `g =
h²` with `h` single-valued (so the period halves to `ph := ∮ d log h` and the closed-loop FTC gives
`exp(ph) = 1`), then `ph = 2πi·n` (integer winding) and `2πi = 2·ph = 2πi·(2n)` forces `1 = 2n` —
impossible. So `g` is **not** a square. This is the complete winding bridge, with exactly two analytic
inputs isolated as hypotheses: the period `2πi = 2·ph` (project: `pathInt_iterate_comp`) and the FTC
`exp ph = 1` (the closed-loop fundamental theorem). Nothing else remains for the per-level monodromy. -/
theorem not_square_of_period_ftc {ph : ℂ}
    (hperiod : 2 * (Real.pi : ℂ) * Complex.I = 2 * ph)
    (hftc : Complex.exp ph = 1) : False := by
  obtain ⟨n, hn⟩ := winding_integer_of_exp_eq_one hftc
  exact not_square_of_odd_period n hperiod hn

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **The deck `K`-algebra automorphism fixes the projection base `K = ℂ(p₀)` at the meroField level.**
Lifting `precompAnalytic_polyToAnalyticVia_fix` through the fraction-field map: when the projection
germ `p₀` is `g`-invariant (`p₀∘g = p₀`), the deck automorphism `precompMeroEquiv` fixes every
`q(p₀) ∈ K` inside `meroField U`. This is exactly the `hK` hypothesis `monoF_witness` requires —
discharged automatically once the base is embedded via the covering projection `p₀` rather than the
identity coordinate. So on the cover annulus (`g` = the order-`2ⁿ` sheet rotation, `p₀` = the `2ⁿ`-fold
covering projection with `p₀∘g = p₀`), the deck is a genuine `K`-automorphism — the planar obstruction
(identity base ⟹ `g = id`) is gone. -/
theorem precompMeroEquiv_polyToAnalyticVia_fix {U : Set ℂ} {g g' : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U} (hp0 : precompAnalytic hg hmaps p₀ = p₀) (q : Polynomial ℂ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap (analyticSubring U) (meroField U) (polyToAnalyticVia U p₀ q))
      = algebraMap (analyticSubring U) (meroField U) (polyToAnalyticVia U p₀ q) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  apply precompMeroEquiv_algebraMap_fix
  rw [← precompAnalytic_coe hg hmaps (polyToAnalyticVia U p₀ q),
      precompAnalytic_polyToAnalyticVia_fix hg hmaps hp0 q]

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **Concrete deck/projection pair on the cover annulus.** On the norm-annulus `Ã = {ρ < |w| < R}`
the `2ⁿ`-fold covering projection `p₀ = w^{2ⁿ}` (`= polyToAnalytic Ã (X^{2ⁿ})`) is invariant under the
order-`2ⁿ` sheet rotation `g = rotation ζ` (`w ↦ ζw`, `|ζ|=1`, `ζ^{2ⁿ}=1`): `p₀∘g = (ζw)^{2ⁿ} =
ζ^{2ⁿ}·w^{2ⁿ} = w^{2ⁿ} = p₀`. So `(g, p₀)` is a concrete realization of the projection-base hypothesis
`p₀∘g = p₀` — combined with `precompMeroEquiv_polyToAnalyticVia_fix`, the rotation deck fixes the whole
base `K = ℂ(w^{2ⁿ}) = ℂ(z)` of the cover carrier `meroField Ã`, with deck order `2ⁿ`. Only the genuine
Böttcher lift `φ̃c` (with `φ̃c∘g = ζ·φ̃c`) now remains to instantiate the disconnected case. -/
theorem precompAnalytic_rotation_coverProj_fix {ρ R : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ = 1) (n : ℕ)
    (hζn : ζ ^ (2 ^ n) = 1) :
    precompAnalytic (analyticOnNhd_rotation ζ {w : ℂ | ρ < ‖w‖ ∧ ‖w‖ < R})
        (rotation_mapsTo_annulus hζ ρ R)
        (polyToAnalytic {w : ℂ | ρ < ‖w‖ ∧ ‖w‖ < R} (Polynomial.X ^ (2 ^ n)))
      = polyToAnalytic {w : ℂ | ρ < ‖w‖ ∧ ‖w‖ < R} (Polynomial.X ^ (2 ^ n)) := by
  apply Subtype.ext
  rw [precompAnalytic_coe]
  show (↑(fun z => (Polynomial.X ^ (2 ^ n) : Polynomial ℂ).eval z) : Germ (𝓟 _) ℂ).compTendsto
      (rotation ζ) _ = ↑(fun z => (Polynomial.X ^ (2 ^ n) : Polynomial ℂ).eval z)
  rw [Germ.coe_compTendsto]
  congr 1
  funext w
  simp only [rotation, Function.comp_apply, Polynomial.eval_pow, Polynomial.eval_X, mul_pow, hζn,
    one_mul]

end Bottcher

namespace Bottcher
open Filter Set

/-- **Germ-level scaling from function-level scaling.** Lifts a pointwise deck-scaling `β(ρ w) = ζ·β w`
(on `U`) of a Böttcher branch `β` to the germ identity `(β).compTendsto ρ = ζ·(β)` in `Germ (𝓟 U) ℂ`.
Since `(constToAnalytic U ζ : Germ) = ↑(fun _ ↦ ζ)`, this is exactly the `hscale` hypothesis that
`monoF_witness`/`hliftF` consume: the bridge from the analytic scaling
(`scaling_from_modulus_preserved`, derived in turn from the lift's mere existence) to the germ-level
monodromy datum the disconnected discharge needs. So the whole `hliftF` scaling chain bottoms out at the
single existence of the cover green-conjugate `F` with `β = exp F`. -/
theorem germ_scaling_of_function_scaling {U : Set ℂ} {β : ℂ → ℂ} {ρ : ℂ → ℂ} {ζ : ℂ}
    (hmaps : Set.MapsTo ρ U U) (hscale : ∀ w ∈ U, β (ρ w) = ζ * β w) :
    (↑β : Germ (𝓟 U) ℂ).compTendsto ρ (tendsto_principal_principal.mpr hmaps)
      = (↑(fun _ : ℂ => ζ) : Germ (𝓟 U) ℂ) * (↑β : Germ (𝓟 U) ℂ) := by
  rw [Germ.coe_compTendsto, ← Germ.coe_mul]
  exact Germ.coe_eq.mpr (Filter.eventually_principal.mpr (fun w hw => hscale w hw))

end Bottcher

namespace Bottcher
open Polynomial Filter

/-- **The cover coordinate scales under the deck — the concrete `hscale`.** On the cover annulus
`Ã = {ρ<|w|<R}`, the natural lift `φ̃c = w` (the identity germ `polyToAnalytic Ã X`) scales by `ζ`
under the deck rotation `g = rotation ζ`: `w∘g = ζ·w`. This is exactly the `hscale` datum
`monoF_witness`/`hliftF` require, realized concretely. Via the Böttcher conjugacy
`φc∘f^[n] = (·)^{2ⁿ}∘φc` (`MonodromyContinuation.isCoveringMap_dyadic`), this cover coordinate `w` IS
the genuine `φc` continued to the cover, and its deck-scaling is the order-`2ⁿ` monodromy multiplier
(`MonodromyMultiplier.multiplier_orderOf_of_mass`). With the projection base `K = ℂ(p₀)`
(`precompAnalytic_rotation_coverProj_fix`) fixed by the same deck, this supplies `monoF_witness` in full
bar the descent identification `w ↦ phiMero`. -/
theorem precompAnalytic_rotation_id_scale {ρ R : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    let U := {w : ℂ | ρ < ‖w‖ ∧ ‖w‖ < R}
    (((polyToAnalytic U Polynomial.X) : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto
        (rotation ζ) (tendsto_principal_principal.mpr (rotation_mapsTo_annulus hζ ρ R))
      = ((constToAnalytic U ζ : analyticSubring U) : Germ (𝓟 U) ℂ)
        * (((polyToAnalytic U Polynomial.X) : analyticSubring U) : Germ (𝓟 U) ℂ) := by
  intro U
  have hlhs : (((polyToAnalytic U Polynomial.X) : analyticSubring U) : Germ (𝓟 U) ℂ).compTendsto
        (rotation ζ) (tendsto_principal_principal.mpr (rotation_mapsTo_annulus hζ ρ R))
      = (↑(fun w : ℂ => ζ * w) : Germ (𝓟 U) ℂ) := by
    show (↑(fun z => (Polynomial.X : Polynomial ℂ).eval z) : Germ (𝓟 U) ℂ).compTendsto (rotation ζ) _
        = ↑(fun w : ℂ => ζ * w)
    rw [Germ.coe_compTendsto]; congr 1; funext w; simp [rotation, Polynomial.eval_X]
  have hrhs : ((constToAnalytic U ζ : analyticSubring U) : Germ (𝓟 U) ℂ)
        * (((polyToAnalytic U Polynomial.X) : analyticSubring U) : Germ (𝓟 U) ℂ)
      = (↑(fun w : ℂ => ζ * w) : Germ (𝓟 U) ℂ) := by
    show (↑(fun _ : ℂ => ζ) : Germ (𝓟 U) ℂ) * ↑(fun z => (Polynomial.X : Polynomial ℂ).eval z)
        = ↑(fun w : ℂ => ζ * w)
    rw [← Germ.coe_mul]; congr 1; funext w; simp [Polynomial.eval_X]
  rw [hlhs, hrhs]

end Bottcher

namespace Bottcher
open Filter Set

/-- **Descent capstone: independence transfers from the cover field to the deep ball.** If the two
Böttcher germs `F, G` are algebraically independent over `ℂ(z)` on the **cover field** `meroField U`,
then their restrictions to a subdomain `V ⊆ U` (the deep ball) are independent over `ℂ(z)` on
`meroField V`. The descent `restrictMeroHom` is an injective `ℂ(z)`-algebra hom
(`restrictMeroHom_ratfuncToMero` + field source), so `noRelation_of_algHom` carries `NoRelation` down:
a polynomial relation among the restricted coordinates would already hold upstairs. This consolidates
the entire descent half — combined with the disconnected discharge on the cover
(`q62_independence_disconnected_of_lifts`, which instantiates `q62_independence`), the genuine
`phiMero c₁, phiMero c₂` on `deepBall` are independent once the cover carries the lift data. Only the
analytic cover `U ⊇ deepBall` with the genuine `φc` germ + monodromy deck remains. Axiom-clean. -/
theorem noRelation_of_restrict {U V : Set ℂ} (hVU : V ⊆ U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    (F G : meroField U)
    (h : haveI := isDomain_analyticSubring U hUo hUc hUne
         haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
         NoRelation (RatFunc ℂ) F G) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ)
      (restrictMeroHom hVU hUo hUc hUne hVo hVc hVne F)
      (restrictMeroHom hVU hUo hUc hUne hVo hVc hVne G) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  haveI := isDomain_analyticSubring V hVo hVc hVne
  letI algU := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  letI algV := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
  let ψ : meroField U →ₐ[RatFunc ℂ] meroField V :=
    { restrictMeroHom hVU hUo hUc hUne hVo hVc hVne with
      commutes' := fun r => RingHom.congr_fun
        (restrictMeroHom_ratfuncToMero hVU hUo hUc hUne hUinf hVo hVc hVne hVinf) r }
  exact noRelation_of_algHom ψ
    (restrictMeroHom hVU hUo hUc hUne hVo hVc hVne).injective h

end Bottcher

namespace Bottcher
open Polynomial Filter Set

/-- **The deck fixes the cover's `ℂ(z)` base at the `RatFunc` level.** For the projection algebra
`ratfuncToMeroVia` (the cover's `K = ℂ(z)` via the deck-invariant projection `p₀`), the deck
automorphism `precompMeroEquiv` fixes every `k ∈ ℂ(z)`: the two ring homs `ℂ(z) → meroField U` agree on
`ℂ[z]` (`precompMeroEquiv_polyToAnalyticVia_fix` lifted through the fraction field), hence are equal
(`IsFractionRing.ringHom_ext`). This is **exactly** the `hliftF`/`hliftG` K-fixing hypothesis
`∀ k : RatFunc ℂ, precompMeroEquiv (algebraMap k) = algebraMap k` that
`q62_independence_disconnected_of_lifts` consumes — discharged for the cover's projection algebra. With
this, every hypothesis of the disconnected discharge except the genuine analytic lift germs `a₁ = φc`
(and `ι`) is mechanically met. -/
theorem precompMeroEquiv_ratfuncToMeroVia_fix {U : Set ℂ} {g g' : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) (hg' : AnalyticOnNhd ℂ g' U)
    (hmaps : Set.MapsTo g U U) (hmaps' : Set.MapsTo g' U U)
    (hgg' : Set.EqOn (g ∘ g') id U) (hg'g : Set.EqOn (g' ∘ g) id U)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {p₀ : analyticSubring U} {f₀ : ℂ → ℂ} (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀)
    (hinf : (f₀ '' U).Infinite)
    (hfix : precompAnalytic hg hmaps p₀ = p₀) (k : RatFunc ℂ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne k)
      = ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne k := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  have key : ((precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne).toRingHom).comp
      (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne)
      = ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
    intro p
    rw [RingHom.comp_apply]
    rw [show ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
        = polyToMeroVia p₀ p from IsFractionRing.lift_algebraMap _ p]
    show precompMeroEquiv hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne
        (algebraMap (analyticSubring U) (meroField U) (polyToAnalyticVia U p₀ p))
      = algebraMap (analyticSubring U) (meroField U) (polyToAnalyticVia U p₀ p)
    exact precompMeroEquiv_polyToAnalyticVia_fix hg hg' hmaps hmaps' hgg' hg'g hUo hUc hUne hfix p
  exact RingHom.congr_fun key k

end Bottcher

namespace Bottcher
open Polynomial Filter Set

/-- **General-descent transfer capstone: cover independence ⟹ deep-ball independence along `ι`.** If
`F, G` are algebraically independent over the cover's projection base `ℂ(p₀)` (= `ratfuncToMeroVia`),
then their pullbacks `precompMeroMap F, precompMeroMap G` along `ι : deepBall → cover` (with `p₀∘ι = z`)
are independent over the deep ball's genuine base `ℂ(z)` (= `ratfuncToMero`). The descent is an injective
`ℂ(z)`-algebra hom (`precompMeroMap_ratfuncToMeroVia` for the `commutes'`, field source for injective),
so `noRelation_of_algHom` carries `NoRelation` down. This is the FULL mechanical reduction of the
disconnected case: with `q62_independence_disconnected_of_lifts` supplying the cover independence (which
instantiates `q62_independence`, discharging `hDisc` from the lift data over `ℂ(p₀)`), and
`precompMeroMap F = phiMero c₁` (the analytic identification), the genuine coordinates are independent.
Every algebraic step is now built and axiom-clean; the lone remaining input is the analytic lift — the
cover `U` with the genuine `φc` germ + deck + the pullback `ι`. -/
theorem noRelation_of_precompMap {U V : Set ℂ} {ι : ℂ → ℂ}
    (hι : AnalyticOnNhd ℂ ι V) (hmaps : Set.MapsTo ι V U) (hUc : IsPreconnected U)
    (hopen : IsOpen (ι '' V)) (hne : (ι '' V).Nonempty)
    (hUo : IsOpen U) (hUne : U.Nonempty)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    {p₀ : analyticSubring U} {f₀ : ℂ → ℂ} (hp0 : (p₀ : Germ (𝓟 U) ℂ) = ↑f₀)
    (hinf : (f₀ '' U).Infinite)
    (hp0ι : (p₀ : Germ (𝓟 U) ℂ).compTendsto ι (tendsto_principal_principal.mpr hmaps)
        = (↑(fun w : ℂ => w) : Germ (𝓟 V) ℂ)) (F G : meroField U)
    (h : haveI := isDomain_analyticSubring U hUo hUc hUne
         haveI := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
         NoRelation (RatFunc ℂ) F G) :
    haveI := isDomain_analyticSubring V hVo hVc hVne
    haveI := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
    NoRelation (RatFunc ℂ)
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne F)
      (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne G) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  haveI := isDomain_analyticSubring V hVo hVc hVne
  letI algU := (ratfuncToMeroVia p₀ hp0 hinf hUo hUc hUne).toAlgebra
  letI algV := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
  let ψ : meroField U →ₐ[RatFunc ℂ] meroField V :=
    { precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne with
      commutes' := fun k => precompMeroMap_ratfuncToMeroVia hι hmaps hUc hopen hne hUo hUne
        hVo hVc hVne hVinf hp0 hinf hp0ι k }
  exact noRelation_of_algHom ψ
    (precompMeroMap hι hmaps hUc hopen hne hUo hUne hVo hVc hVne).injective h

end Bottcher
