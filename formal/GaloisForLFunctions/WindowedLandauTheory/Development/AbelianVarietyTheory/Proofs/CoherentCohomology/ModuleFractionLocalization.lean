import Mathlib.Algebra.Module.LocalizedModule.Exact

/-! Fractions with a power denominator in a localized module. -/

noncomputable section

namespace GlobalTheory.ModuleFraction

open LocalizedModule

variable {A : Type*} [CommRing A] {M N P : Type*}
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]

def frac (f : A) (k : ℕ) : M →ₗ[A] LocalizedModule.Away f M :=
  divBy (⟨f ^ k, k, rfl⟩ : Submonoid.powers f) ∘ₗ mkLinearMap (Submonoid.powers f) M

theorem frac_apply (f : A) (k : ℕ) (m : M) :
    frac f k m = mk m (⟨f ^ k, k, rfl⟩ : Submonoid.powers f) := by
  simp [frac, liftOn_mk]

theorem frac_zero (f : A) : frac (M := M) f 0 = mkLinearMap (Submonoid.powers f) M := by
  apply LinearMap.ext
  intro m
  rw [frac_apply, mkLinearMap_apply]
  congr 1
  exact Subtype.ext (pow_zero f)

theorem exists_frac {f : A} (z : LocalizedModule.Away f M) : ∃ k m, frac f k m = z := by
  induction z using LocalizedModule.induction_on with
  | _ m s =>
    obtain ⟨_, k, rfl⟩ := s
    exact ⟨k, m, frac_apply f k m⟩

theorem frac_eq_iff {f : A} {k j : ℕ} {m m' : M} :
    frac f k m = frac f j m' ↔ ∃ l : ℕ, f ^ (l + j) • m = f ^ (l + k) • m' := by
  rw [frac_apply, frac_apply, LocalizedModule.mk_eq]
  constructor
  · rintro ⟨⟨_, l, rfl⟩, h⟩
    exact ⟨l, by simpa only [pow_add, mul_smul, Submonoid.smul_def] using h⟩
  · rintro ⟨l, h⟩
    exact ⟨⟨_, l, rfl⟩, by simpa only [pow_add, mul_smul, Submonoid.smul_def] using h⟩

theorem frac_eq_zero_iff {f : A} {k : ℕ} {m : M} :
    frac f k m = 0 ↔ ∃ l : ℕ, f ^ l • m = 0 := by
  rw [← map_zero (frac f 0), frac_eq_iff]
  simp

theorem frac_add_pow_smul (f : A) (k j : ℕ) (m : M) :
    frac f (k + j) (f ^ j • m) = frac f k m :=
  frac_eq_iff.2 ⟨0, by simp [pow_add, mul_smul]⟩

theorem pow_smul_frac (f : A) (k : ℕ) (m : M) :
    f ^ k • frac f k m = frac f 0 m := by
  rw [← map_smul, ← frac_add_pow_smul f 0 k, zero_add]

/-- A divisor of the element being inverted acts invertibly on the localized module. -/
theorem isUnit_smul_of_dvd {f g : A} (h : f ∣ g) :
    IsUnit (algebraMap A (Module.End A (LocalizedModule.Away g M)) f) := by
  have hg : IsUnit (algebraMap A (Module.End A (LocalizedModule.Away g M)) g) :=
    IsLocalizedModule.map_units (mkLinearMap (Submonoid.powers g) M)
      (⟨g, 1, pow_one g⟩ : Submonoid.powers g)
  obtain ⟨c, rfl⟩ := h
  rw [map_mul] at hg
  exact ((Commute.isUnit_mul_iff (Algebra.commutes f _)).1 hg).1

private theorem restriction_units {f g : A} (h : f ∣ g) (x : Submonoid.powers f) :
    IsUnit (algebraMap A (Module.End A (LocalizedModule.Away g M)) (x : A)) := by
  obtain ⟨_, k, rfl⟩ := x
  rw [map_pow]
  exact (isUnit_smul_of_dvd (M := M) h).pow k

/-- Restrict to a principal open contained in the original principal open. -/
def restrict {f g : A} (h : f ∣ g) : LocalizedModule.Away f M →ₗ[A] LocalizedModule.Away g M :=
  LocalizedModule.lift (Submonoid.powers f) (mkLinearMap (Submonoid.powers g) M) (restriction_units h)

theorem restrict_comp_mkLinearMap {f g : A} (h : f ∣ g) :
    restrict h ∘ₗ mkLinearMap (Submonoid.powers f) M = mkLinearMap (Submonoid.powers g) M :=
  LocalizedModule.lift_comp _ _ _

theorem restrict_frac_zero {f g : A} (h : f ∣ g) (m : M) :
    restrict h (frac f 0 m) = frac g 0 m := by
  rw [frac_zero, frac_zero]
  exact LinearMap.congr_fun (restrict_comp_mkLinearMap h) m

theorem restrict_frac {f g c : A} (h : f ∣ g) (hg : g = c * f) (k : ℕ) (m : M) :
    restrict h (frac f k m) = frac g k (c ^ k • m) := by
  apply IsLocalizedModule.smul_injective (mkLinearMap (Submonoid.powers g) M)
    (⟨g ^ k, k, rfl⟩ : Submonoid.powers g)
  change g ^ k • restrict h (frac f k m) = g ^ k • frac g k (c ^ k • m)
  calc
    _ = c ^ k • restrict h (f ^ k • frac f k m) := by
      rw [show g ^ k = c ^ k * f ^ k by rw [hg, mul_pow], mul_smul, map_smul]
    _ = _ := by rw [pow_smul_frac, restrict_frac_zero, pow_smul_frac, map_smul]

theorem restrict_self (f : A) : restrict (M := M) (dvd_refl f) = LinearMap.id :=
  LocalizedModule.lift_unique _ _ _ _ rfl

theorem restrict_comp {f g t : A} (h : f ∣ g) (h' : g ∣ t) :
    restrict (M := M) h' ∘ₗ restrict h = restrict (h.trans h') :=
  (LocalizedModule.lift_unique _ _ _ _ (by
    rw [LinearMap.comp_assoc, restrict_comp_mkLinearMap, restrict_comp_mkLinearMap])).symm

def map (f : A) (φ : M →ₗ[A] N) : LocalizedModule.Away f M →ₗ[A] LocalizedModule.Away f N :=
  IsLocalizedModule.map (Submonoid.powers f) (mkLinearMap _ M) (mkLinearMap _ N) φ

@[simp]
theorem map_frac (f : A) (φ : M →ₗ[A] N) (k : ℕ) (m : M) :
    map f φ (frac f k m) = frac f k (φ m) := by
  rw [frac_apply, frac_apply]
  exact IsLocalizedModule.map_LocalizedModules _ _ _ _

theorem map_restrict {f g : A} (h : f ∣ g) (φ : M →ₗ[A] N) (z : LocalizedModule.Away f M) :
    map g φ (restrict h z) = restrict h (map f φ z) := by
  obtain ⟨k, m, rfl⟩ := exists_frac z
  obtain ⟨c, hc⟩ := exists_eq_mul_left_of_dvd h
  rw [restrict_frac h hc, map_frac, map_frac, restrict_frac h hc, map_smul]

theorem map_injective_of {f : A} {φ : M →ₗ[A] N}
    (h : ∀ m, φ m = 0 → ∃ k : ℕ, f ^ k • m = 0) : Function.Injective (map f φ) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨k, m, rfl⟩ := exists_frac z
  rw [map_frac, frac_eq_zero_iff] at hz
  obtain ⟨l, hl⟩ := hz
  obtain ⟨j, hj⟩ := h _ ((map_smul φ _ _).trans hl)
  exact frac_eq_zero_iff.2 ⟨j + l, by rw [pow_add, mul_smul, hj]⟩

theorem map_surjective_of {f : A} {φ : M →ₗ[A] N}
    (h : ∀ y, ∃ k : ℕ, f ^ k • y ∈ LinearMap.range φ) : Function.Surjective (map f φ) := by
  intro z
  obtain ⟨k, y, rfl⟩ := exists_frac z
  obtain ⟨j, m, hm⟩ := h y
  exact ⟨frac f (k + j) m, by rw [map_frac, hm, frac_add_pow_smul]⟩

theorem map_exact (f : A) {φ : M →ₗ[A] N} {ψ : N →ₗ[A] P} (h : Function.Exact φ ψ) :
    Function.Exact (map f φ) (map f ψ) :=
  IsLocalizedModule.map_exact _ _ _ _ _ _ h

end GlobalTheory.ModuleFraction
