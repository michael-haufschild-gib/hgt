/-
# `meroField`-germ nonvanishing ⟹ countable zeros (natural-boundary blueprint, step 3)

Bridge for the transcendence chain (`STATUS.md` blueprint): when an analytic-germ element of the
meromorphic field `meroField U` is nonzero (e.g. `∂_Y P(φ_c) ≠ 0`, which holds for the SIMPLE root of a
separable minimal polynomial via `Separable.aeval_derivative_ne_zero`), the representative function is
`≢ 0` on `U`, hence its zeros are countable (`ZeroSet.analyticOnNhd_zeros_countable`). So COFINITELY many
points of `U` are simple-root points where `AlgebraicBranch.exists_analyticAt_branch` continues `φ_c`.
Combines `MeromorphicField`'s faithfulness (`meroField_germ_eq_zero_iff`) with the countable-zeros lemma.
-/
import GaloisForLFunctions.Bottcher.MeromorphicField
import GaloisForLFunctions.Bottcher.ZeroSet
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Algebraic.Basic

open Filter Topology

namespace Bottcher

/-- **A nonzero analytic-germ element of `meroField U` has a representative nonvanishing somewhere.**
Contrapositive of the faithfulness `meroField_germ_eq_zero_iff`: if `algebraMap (germ f) ≠ 0` then `f`
does not vanish identically on the connected open `U`. -/
theorem exists_ne_zero_of_germ_ne_zero {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hne : haveI := isDomain_analyticSubring U hUo hUc hUne
      algebraMap (analyticSubring U) (meroField U)
        ⟨Germ.coeRingHom (𝓟 U) f, ⟨f, hf, rfl⟩⟩ ≠ 0) :
    ∃ z ∈ U, f z ≠ 0 := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  by_contra hcon
  push Not at hcon
  exact hne ((meroField_germ_eq_zero_iff U hUo hUc hUne hf).mpr (fun z hz => by simp [hcon z hz]))

/-- **Germ nonvanishing in `meroField U` ⟹ countable zero set** (blueprint step 3). For `f` analytic on
a connected open `U` whose `meroField` germ is nonzero, the zeros `{z ∈ U | f z = 0}` are countable. The
transcendence chain applies this to `f = ∂_Y P(·, φ_c ·)` (nonzero germ by simplicity of the root),
yielding that `φ_c` is a simple root of `P(z,·)` at cofinitely many points of `U`. -/
theorem analyticGerm_ne_zero_zeros_countable {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hne : haveI := isDomain_analyticSubring U hUo hUc hUne
      algebraMap (analyticSubring U) (meroField U)
        ⟨Germ.coeRingHom (𝓟 U) f, ⟨f, hf, rfl⟩⟩ ≠ 0) :
    {z ∈ U | f z = 0}.Countable := by
  obtain ⟨x₀, hx₀U, hx₀⟩ := exists_ne_zero_of_germ_ne_zero hUo hUc hUne hf hne
  exact analyticOnNhd_zeros_countable hf hUc hx₀U hx₀

/-- **Algebraic ⟹ a separable witness with nonzero derivative at the root** (blueprint steps 1–2,
abstract core). For `g` algebraic over a char-0 field `K`, its minimal polynomial `q` is separable, so
`g` is a SIMPLE root: `aeval g q = 0` and `aeval g (derivative q) ≠ 0`. Applied to `g = φ_c`, `K =
ℂ(z)`, this is what feeds `analyticGerm_ne_zero_zeros_countable` (the value-germ `∂_Y q(φ_c) ≠ 0`) and
then `AlgebraicBranch.exists_analyticAt_branch`. -/
theorem exists_separable_witness {K M : Type*} [Field K] [Field M] [Algebra K M] [CharZero K]
    {g : M} (hg : ¬ Transcendental K g) :
    ∃ q : Polynomial K, q ≠ 0 ∧ Polynomial.aeval g q = 0 ∧
      Polynomial.aeval g (Polynomial.derivative q) ≠ 0 := by
  have halg : IsAlgebraic K g := not_not.mp hg
  have hint : IsIntegral K g := halg.isIntegral
  refine ⟨minpoly K g, minpoly.ne_zero hint, minpoly.aeval K g, ?_⟩
  exact (minpoly.irreducible hint).separable.aeval_derivative_ne_zero (minpoly.aeval K g)

/-- **Meromorphic analytic representation with countable-zero numerator/denominator** (blueprint step-5
sub-piece i). Any nonzero element `y` of `meroField U` is `⟦fp⟧/⟦fq⟧` for analytic `fp, fq` on `U`, each
with a COUNTABLE zero set. So off a countable set, `y`'s value is a genuine nonzero ratio `fp/fq` — the
handle for the meromorphic value `aeval (φ_c germ) (∂_Y q)` in the transcendence bridge (cofinitely many
points where it is a nonzero analytic value, hence `φ_c` a simple root there). -/
theorem meroField_repr_countable {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (y : meroField U)
    (hy : haveI := isDomain_analyticSubring U hUo hUc hUne; y ≠ 0) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    ∃ (fp fq : ℂ → ℂ) (hfp : AnalyticOnNhd ℂ fp U) (hfq : AnalyticOnNhd ℂ fq U),
      y = algebraMap (analyticSubring U) (meroField U) ⟨Germ.coeRingHom (𝓟 U) fp, fp, hfp, rfl⟩ /
          algebraMap (analyticSubring U) (meroField U) ⟨Germ.coeRingHom (𝓟 U) fq, fq, hfq, rfl⟩ ∧
      {z ∈ U | fp z = 0}.Countable ∧ {z ∈ U | fq z = 0}.Countable := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := analyticSubring U) y
  have hqunit : IsUnit (algebraMap (analyticSubring U) (meroField U) q) :=
    IsLocalization.map_units (meroField U) ⟨q, hq⟩
  have hp0 : p ≠ 0 := by
    intro h; apply hy; rw [← hpq, h, map_zero, zero_div]
  have hq0 : q ≠ 0 := fun h => hqunit.ne_zero (by rw [h, map_zero])
  obtain ⟨fp, hfp, hfpe⟩ := p.2
  obtain ⟨fq, hfq, hfqe⟩ := q.2
  have hpe : (⟨Germ.coeRingHom (𝓟 U) fp, fp, hfp, rfl⟩ : analyticSubring U) = p := Subtype.ext hfpe
  have hqe : (⟨Germ.coeRingHom (𝓟 U) fq, fq, hfq, rfl⟩ : analyticSubring U) = q := Subtype.ext hfqe
  have hinj := IsFractionRing.injective (analyticSubring U) (meroField U)
  refine ⟨fp, fq, hfp, hfq, ?_, ?_, ?_⟩
  · rw [hpe, hqe]; exact hpq.symm
  · refine analyticGerm_ne_zero_zeros_countable hUo hUc hUne hfp ?_
    rw [hpe]; exact fun h => hp0 (hinj (by rw [h, map_zero]))
  · refine analyticGerm_ne_zero_zeros_countable hUo hUc hUne hfq ?_
    rw [hqe]; exact fun h => hq0 (hinj (by rw [h, map_zero]))

end Bottcher
