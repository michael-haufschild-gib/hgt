import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WildResidualUnipotence
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WildInertiaSubgroup

/-! At an auxiliary place of distinct characteristic the twist character
has prime-to-residue-characteristic order. The adic rank-one character
therefore kills wild inertia. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TameKummer

namespace WindowedLandauTheory.NormalizedTypes

variable (D : D7) (i : D.nd.Loc) (k : Fin 2)
local notation "Γ" => (D.nd.Om ≃ₐ[D.host.E] D.nd.Om)
local notation "ℓ" => D.nd.l i

/-- A place above an auxiliary prime different from the coefficient
characteristic is away from the coefficient prime. -/
theorem auxiliary_place_away (hk : ℓ ≠ D.host.g k)
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    w ∉ placesOver D.host.E ℓ := by
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hcop := (Nat.coprime_primes (D.host.g_prime k) (D.nd.lPrime i).out).mpr hk.symm
  have hp : (D.nd.plOm.1 w).valuation (D.host.g k : D.nd.Om) < 1 := by
    simpa using (D.nd.plOm.2 w (D.host.g k : 𝓞 D.host.E)).mpr hw
  intro hl
  exact natCast_valuation_not_lt_one _ hp hcop
    (by simpa using (D.nd.plOm.2 w (ℓ : 𝓞 D.host.E)).mpr hl)

/-- The prime-to-auxiliary-characteristic order bound forces the normalized
rank-one character to be tame. -/
theorem chi_eq_one_on_auxiliary_wild (hk : ℓ ≠ D.host.g k)
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.host.g k))
    {s : Γ} (hs : s ∈ wildInertia (E := D.host.E) (D.nd.plOm.1 w)) :
    D.nd.chi i 1 s = 1 := by
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  let A := D.nd.plOm.1 w
  have hi := wildInertia_le_inertia A hs
  have hy : w ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf i)) := by
    rw [D.ntw.twOf_l]
    exact auxiliary_place_away D i k hk w hw
  have ht := D.ntw.twistCharacterFamily_tame (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) k w
    hw hy A (D.nd.plOm.2 w) s hi
  obtain ⟨n, hn⟩ := D.ntw.psiL_ord i s
  let θ := (Units.map (D.ntw.twist₂ i).toMonoidHom).comp
    (D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i))
  have hθ : θ s ^ (D.host.g k - 1) = 1 := by
    change Units.map _ (D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) s) ^ _ = 1
    rw [← map_pow, ht, map_one]
  have hpow : D.nd.chi i 1 s ^ ((D.host.g k - 1) * ℓ ^ n) = 1 := by
    rw [D.ntw.chi_tw i]
    change (θ s * D.ntw.psiL i s) ^ ((D.host.g k - 1) * ℓ ^ n) = 1
    rw [mul_pow, pow_mul, hθ, one_pow, one_mul, pow_mul', hn, one_pow]
  have hp : A.valuation (D.host.g k : D.nd.Om) < 1 := by
    simpa using (D.nd.plOm.2 w (D.host.g k : 𝓞 D.host.E)).mpr hw
  have hc := (Nat.coprime_primes (D.host.g_prime k) (D.nd.lPrime i).out).mpr hk.symm
  have hpred : (D.host.g k).Coprime (D.host.g k - 1) := by
    simpa only [pow_one] using (coprime_pow_sub_one (p := D.host.g k) (d := 1) Nat.one_pos)
  exact character_eq_one_of_wild_of_pow_eq_one A (D.nd.O_adic i) (D.nd.chi i 1) (D.nd.chi_cont i 1) hs
    (natCast_valuation_not_lt_one A hp (hpred.mul_right (hc.pow_right n))) hpow

end WindowedLandauTheory.NormalizedTypes
