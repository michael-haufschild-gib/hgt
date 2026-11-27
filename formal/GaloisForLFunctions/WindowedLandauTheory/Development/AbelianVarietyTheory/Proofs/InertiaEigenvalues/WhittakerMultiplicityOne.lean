import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabels
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GelfandGraevNorm
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerAdditiveScale
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerVectors
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialLabels

/-! There are as many generic polynomial labels as the squared Gelfand–Graev
norm. Multiplicity greater than one would leave too small a norm after
subtracting that irreducible character once. -/

noncomputable section
open GaloisForLFunctions Polynomial
open scoped Classical

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

private theorem exists_generic_finset (L : LabelDatum g) (hg : 5 ≤ g) (hn : 0 < n) :
    ∃ S : Finset (Gn g n → ℂ), S.card = g ^ n - g ^ (n - 1) ∧
      ∀ χ ∈ S, IsIrr χ ∧ wh ZMod.stdAddChar χ ≠ 0 := by
  let P : Set (ZMod g)[X] := {f | f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0}
  obtain ⟨hcard, hfin⟩ := GlobalTheory.GrPolys.card_monic_coeff_zero_ne_zero g n hn
  have hex (f : P) : ∃ χ : Gn g n → ℂ, IsIrr χ ∧ HasLabel L χ f.val ∧ wh ZMod.stdAddChar χ ≠ 0 :=
    exists_generic_of_polynomial_label L f.val f.property.1 f.property.2.1 f.property.2.2
  let F (f : P) := (hex f).choose
  have hF (f : P) : IsIrr (F f) ∧ HasLabel L (F f) f.val ∧ wh ZMod.stdAddChar (F f) ≠ 0 :=
    (hex f).choose_spec
  have hinj : Function.Injective F := by
    intro f f' he
    apply Subtype.ext
    apply hasLabel_unique L hg (hF f).1 (hF f).2.1
    rw [he]
    exact (hF f').2.1
  change P.ncard = _ at hcard
  have hfin' : P.Finite := hfin
  let lift (f : hfin'.toFinset) := F ⟨f.val, (Set.Finite.mem_toFinset _).mp f.property⟩
  have hlift : Function.Injective lift := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun f : P => f.val) (hinj he)
  let S := hfin'.toFinset.attach.image lift
  refine ⟨S, ?_, ?_⟩
  · change (hfin'.toFinset.attach.image lift).card = _
    rw [Finset.card_image_of_injective _ hlift,
      Finset.card_attach, ← Set.ncard_eq_toFinset_card P hfin']
    exact hcard
  · intro χ hχ
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hχ
    exact ⟨(hF _).1, (hF _).2.2⟩

private theorem pairing_gg (ψ : AddChar (ZMod g) ℂ) (χ : Gn g n → ℂ) (hχ : IsClass χ) :
    characterPairing (Gn g n) (gg ψ n) χ = wh ψ χ := by
  rw [← ip_gg ψ n χ hχ, ip, characterPairing, Nat.card_eq_fintype_card]

private theorem wh_standard_eq_one (L : LabelDatum g) (hg : 5 ≤ g) (hn : 0 < n)
    {χ : Gn g n → ℂ} (hχ : IsIrr χ) (hw : wh ZMod.stdAddChar χ ≠ 0) :
    wh ZMod.stdAddChar χ = 1 := by
  let ψ : AddChar (ZMod g) ℂ := ZMod.stdAddChar
  let γ := gg ψ n
  have hψ : ψ ≠ 1 := stdAddChar_ne_one
  have hγcls : IsClass γ := fun x y => by
    change gg ψ n (y * x * y⁻¹) = gg ψ n x
    rw [gg_eq_inducedFunction]
    exact inducedFunction_conj (upperUnitriangular g n) _ y x
  have hγv : γ ∈ virtualCharacterGroup (Gn g n) := by
    change gg ψ n ∈ virtualCharacterGroup (Gn g n)
    rw [gg_eq_monomialCharacter]
    exact genuineCharacterMonoid_le_virtualCharacterGroup _
      (monomialGenuineCharacter _ _ (whittakerCharacter ψ n)).property
  obtain ⟨V, hV, hVχ⟩ := hχ
  have hχ' : χ ∈ CuspGL.simpleCharacterSet (Gn g n) := ⟨V, hV, funext hVχ⟩
  have hχcls : IsClass χ := fun x y =>
    (hVχ (y * x * y⁻¹)).symm.trans ((V.char_conj x y).trans (hVχ x))
  have hχv : χ ∈ virtualCharacterGroup (Gn g n) := AddSubgroup.subset_closure ⟨V, funext hVχ⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, wh ψ χ = (d : ℂ) := by
    rw [← funext hVχ, wh_eq_finrank]
    exact ⟨_, rfl⟩
  have hd0 : d ≠ 0 := fun h => hw (by simpa only [h, Nat.cast_zero] using hd)
  by_contra hn1
  have hd2 : 2 ≤ d := by
    have hd1 : d ≠ 1 := fun h => hn1 (by simpa only [h, Nat.cast_one] using hd)
    omega
  obtain ⟨S, hScard, hS⟩ := exists_generic_finset L hg hn
  have hd' : characterPairing (Gn g n) γ χ = (d : ℂ) := (pairing_gg ψ χ hχcls).trans hd
  have hnorm : characterPairing (Gn g n) γ γ = (S.card : ℂ) := by
    change characterPairing (Gn g n) (gg ψ n) (gg ψ n) = _
    rw [pairing_gg ψ (gg ψ n) hγcls, GGNorm.wh_gg ψ hψ n hn, hScard,
      Nat.cast_sub (Nat.pow_le_pow_right (Fact.out : g.Prime).pos (Nat.sub_le n 1)),
      Nat.cast_pow, Nat.cast_pow]
  have hχnorm : characterPairing (Gn g n) χ χ = 1 :=
    (CuspGL.pairing_simple hχ' hχ').trans (if_pos rfl)
  have hsym : characterPairing (Gn g n) χ γ = (d : ℂ) :=
    (characterPairing_comm _ _ _).trans hd'
  let δ := γ - χ
  have hδv : δ ∈ virtualCharacterGroup (Gn g n) := sub_mem hγv hχv
  have hδnorm : characterPairing (Gn g n) δ δ = (S.card : ℂ) + 1 - 2 * (d : ℂ) := by
    simp only [δ, sub_eq_add_neg, characterPairing_add_left, characterPairing_add_right,
      characterPairing_neg_left, characterPairing_neg_right]
    rw [hnorm, hd', hsym, hχnorm]
    ring
  have hδnz (η : Gn g n → ℂ) (hη : η ∈ S) :
      η ∈ CuspGL.simpleCharacterSet (Gn g n) ∧ characterPairing (Gn g n) δ η ≠ 0 := by
    obtain ⟨⟨W, hW, hWη⟩, hwη⟩ := hS η hη
    have hη' : η ∈ CuspGL.simpleCharacterSet (Gn g n) := ⟨W, hW, funext hWη⟩
    refine ⟨hη', ?_⟩
    by_cases he : χ = η
    · rw [← he]
      simp only [δ, sub_eq_add_neg, characterPairing_add_left, characterPairing_neg_left]
      rw [hd', hχnorm, ← sub_eq_add_neg, sub_ne_zero, ← Nat.cast_one]
      exact fun h => (by omega : d ≠ 1) (Nat.cast_inj.mp h)
    · have hηcls : IsClass η := fun x y =>
        (hWη (y * x * y⁻¹)).symm.trans ((W.char_conj x y).trans (hWη x))
      have hpair : characterPairing (Gn g n) γ η = wh ψ η := pairing_gg ψ η hηcls
      simp only [δ, sub_eq_add_neg, characterPairing_add_left, characterPairing_neg_left]
      rw [CuspGL.pairing_simple hχ' hη', if_neg he, neg_zero, add_zero, hpair]
      exact hwη
  have he := CuspGL.card_le_pairing_of_nonzero_on_simple hδv S hδnz
  have hre : ((S.card : ℂ) + 1 - 2 * (d : ℂ)).re = (S.card : ℝ) + 1 - 2 * (d : ℝ) := by
    norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re]
  rw [hδnorm, hre] at he
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  linarith only [he, hdR]

/-- A generic irreducible character has Whittaker multiplicity one. -/
theorem wh_eq_one_of_generic (L : LabelDatum g) (hg : 5 ≤ g) (hn : 0 < n)
    (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) {χ : Gn g n → ℂ}
    (hχ : IsIrr χ) (hw : wh ZMod.stdAddChar χ ≠ 0) : wh ψ χ = 1 := by
  have hcls : IsClass χ := by
    obtain ⟨V, _, hV⟩ := hχ
    intro x y
    exact (hV (y * x * y⁻¹)).symm.trans ((V.char_conj x y).trans (hV x))
  rw [wh_eq_standard ψ hψ χ hcls]
  exact wh_standard_eq_one L hg hn hχ hw

end GlobalTheory.GLq
