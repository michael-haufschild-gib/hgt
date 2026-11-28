import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WildResidualUnipotence
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WildInertiaSubgroup
import Mathlib.Data.Nat.Factorization.Basic

/-! A wild inertia element has prime-power order in each finite quotient.
A smooth inertia character of exponent prime to the residue
characteristic therefore kills wild inertia. -/

noncomputable section

open NumberField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open Topology

namespace GlobalTheory.TameKummer

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  (A : ValuationSubring Ω) {p : ℕ} [Fact p.Prime]

theorem exists_primePower_mem_of_mem_wildInertia (hp : A.valuation (p : Ω) < 1)
    {s : Gal(Ω/E)} (hs : s ∈ wildInertia A)
    (U : Set Gal(Ω/E)) (hU : U ∈ 𝓝 (1 : Gal(Ω/E))) :
    ∃ r : ℕ, s ^ (p ^ r) ∈ U := by
  obtain ⟨L, hL, hnL, hLU⟩ := (krullTopology_mem_nhds_one_iff_of_normal E Ω U).mp hU
  letI := hL
  letI := hnL
  let rL : Gal(Ω/E) →* Gal(L/E) := AlgEquiv.restrictNormalHom L
  let d := orderOf (rL s)
  have hd : d ≠ 0 := (orderOf_pos (rL s)).ne'
  let r := d.factorization p
  let m := ordCompl[p] d
  have hdm : p ^ r * m = d := Nat.ordProj_mul_ordCompl_eq_self d p
  have hm : ¬ A.valuation (m : Ω) < 1 :=
    natCast_valuation_not_lt_one A hp (Nat.coprime_ordCompl (Fact.out : p.Prime) hd)
  have hpow : (s ^ (p ^ r)) ^ m ∈ L.fixingSubgroup := by
    rw [← L.restrictNormalHom_ker, MonoidHom.mem_ker]
    change rL ((s ^ (p ^ r)) ^ m) = 1
    rw [← pow_mul, hdm, map_pow, pow_orderOf_eq_one]
  have hWild : s ^ (p ^ r) ∈ wildInertia A := (wildInertia A).pow_mem hs _
  exact ⟨r, hLU (mem_of_wild_pow_mem A L.fixingSubgroup L.fixingSubgroup_isOpen
    _ ((mem_wildInertia_iff _ _).mp hWild) hm hpow)⟩

theorem inertiaHom_eq_one_of_wild_of_coprime_exponent (hp : A.valuation (p : Ω) < 1)
    {H : Type*} [Group H] (f : Ine (F := E) A →* H) (hf : IsOpen (f.ker : Set (Ine (F := E) A)))
    {n : ℕ} (hn : p.Coprime n) (hexp : ∀ s, f s ^ n = 1)
    (s : Ine (F := E) A) (hs : s.val ∈ wildInertia A) : f s = 1 := by
  have hN : (f.ker : Set (Ine (F := E) A)) ∈ 𝓝 (1 : Ine (F := E) A) :=
    hf.mem_nhds f.ker.one_mem
  rw [IsEmbedding.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hN
  obtain ⟨U, hU, hsub⟩ := hN
  obtain ⟨r, hr⟩ := exists_primePower_mem_of_mem_wildInertia A hp hs U hU
  have hfr : f (s ^ (p ^ r)) = 1 := MonoidHom.mem_ker.mp (hsub hr)
  rw [map_pow] at hfr
  have h1 := orderOf_dvd_of_pow_eq_one hfr
  have h2 := orderOf_dvd_of_pow_eq_one (hexp s)
  have hd := Nat.dvd_gcd h1 h2
  rw [(hn.pow_left r).gcd_eq_one] at hd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

end GlobalTheory.TameKummer

#print axioms GlobalTheory.TameKummer.exists_primePower_mem_of_mem_wildInertia
#print axioms GlobalTheory.TameKummer.inertiaHom_eq_one_of_wild_of_coprime_exponent
