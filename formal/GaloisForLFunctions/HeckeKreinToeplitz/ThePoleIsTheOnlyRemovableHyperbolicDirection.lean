import GaloisForLFunctions.HeckeKreinToeplitz.TheSelectivityBatteryOnPrimeTowers
import GaloisForLFunctions.RHTower.WeilFullConeSpectralConsistency
import GaloisForLFunctions.HeckeKreinToeplitz.WeilsIndexIsCountedByTheOuterFrobeniusEigenvalues

/-!
# The pole is the only removable hyperbolic direction

On a prime tower the Weil kernel splits into its local constituents (`towerKernel_eq_parts`):

`K = Pole − Prime + Arch`,

the pole part `k̂(i/2) e^{−s/2} + k̂(−i/2) e^{s/2}`, the prime part `Σ_n λ(n) n^{−1/2}(k(log n − s) +
k(−log n − s))` and the archimedean part, each read at the lag `s = −nℓ` of the tower kernel
(`towerPole`, `towerPrime`, `towerArch`).

**The pole is one hyperbolic plane** (`hermQuad_gram_towerPole`). Along the tower the pole part is
`A w^n + B w^{−n}` with `w = e^{ℓ/2}`, and its Toeplitz form is `2 Re(ω E(c) conj F(c))`,
`E(c) = Σ c_a w^{n_a}`, `F(c) = Σ c_a w^{−n_a}`, `ω = (A + B̄)/2`: the form of the hyperbolic pair
`h_{w,ω}`. Hence it has at most one negative square (`negIndex_towerPole_le_one`) and vanishes on the
**pole hyperplane** `E(c) = 0`.

**One linear condition costs at most one square** (`hermNegIndex_le_add_one_of_eq_on_ker`). Two forms
that agree on the kernel of a linear functional have negative indices differing by at most one. So
the index of the Weil kernel on a tower and the index of `Arch − Prime` differ by at most one
(`negIndex_towerKernel_le_archPrime_add_one`, `negIndex_archPrime_le_towerKernel_add_one`). The
pole is removable by one linear condition; every other negative square must be paid by the prime
and archimedean constituents together, and none of them is positive alone.
-/

open Complex Finset
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (paperFT_translate)
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity (lagW)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

local notation "Tr" => ArithmeticCastelnuovoSeveri.translate

/-! ### One linear condition costs at most one negative square -/

/-- **Two forms agreeing on a hyperplane have indices differing by at most one.** -/
theorem hermNegIndex_le_add_one_of_eq_on_ker {ι : Type*} [Fintype ι] (H H' : Matrix ι ι ℂ)
    (φ : (ι → ℂ) →ₗ[ℂ] ℂ) (h : ∀ c, φ c = 0 → hermQuad H c = hermQuad H' c) :
    hermNegIndex H ≤ hermNegIndex H' + 1 := by
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  set ψ := φ.domRestrict W
  have hsum := LinearMap.finrank_range_add_finrank_ker ψ
  have hrange : Module.finrank ℂ (LinearMap.range ψ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range ψ)
    rwa [Module.finrank_self] at this
  -- the kernel of `φ` on `W` maps injectively into `ι → ℂ` and is negative for `H'`
  set V := (LinearMap.ker ψ).map W.subtype
  have hV : Module.finrank ℂ V = Module.finrank ℂ (LinearMap.ker ψ) :=
    LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ W.injective_subtype _).symm
  have hneg : IsPosDefOn (-H') V := by
    rintro y ⟨w, hw, rfl⟩ hy
    have hφ : φ (w : ι → ℂ) = 0 := hw
    have hne : ((w : W) : ι → ℂ) ≠ 0 := hy
    have := hW _ w.2 hne
    rw [hermQuad_neg] at this ⊢
    simp only [Submodule.subtype_apply]
    rw [← h _ hφ]
    exact this
  have h1 := finrank_le_posIndex hneg
  rw [hV] at h1
  show hermPosIndex (-H) ≤ hermPosIndex (-H') + 1
  rw [← hrank]
  omega

/-! ### The local constituents on a prime tower -/

variable (lam : ℕ → ℝ) (g : ℝ → ℂ) (ℓ : ℝ)

/-- The pole constituent of the tower kernel. -/
def towerPole : Multiplicative ℤ → ℂ :=
  fun n => RHTower.WeilSpectral.polePart (Tr (-((Multiplicative.toAdd n : ℤ) : ℝ) * ℓ) (EF.weilTest g g))

/-- The prime constituent of the tower kernel. -/
def towerPrime : Multiplicative ℤ → ℂ :=
  fun n => RHTower.WeilSpectral.primePart lam (Tr (-((Multiplicative.toAdd n : ℤ) : ℝ) * ℓ) (EF.weilTest g g))

/-- The archimedean constituent of the tower kernel. -/
def towerArch : Multiplicative ℤ → ℂ :=
  fun n => RHTower.WeilSpectral.archPart (Tr (-((Multiplicative.toAdd n : ℤ) : ℝ) * ℓ) (EF.weilTest g g))

/-- **The tower kernel is pole minus prime plus archimedean.** -/
theorem towerKernel_eq_parts (n : Multiplicative ℤ) :
    towerKernel lam g ℓ n = towerPole g ℓ n - towerPrime lam g ℓ n + towerArch g ℓ n := by
  rw [towerKernel, lagW, RHTower.WeilSpectral.weilFullFunctional_eq_parts]
  rfl

/-- The pole weight `ω = (k̂(i/2) + conj k̂(−i/2))/2`. -/
def poleWeight : ℂ :=
  (paperFT (EF.weilTest g g) (I / 2) + conj (paperFT (EF.weilTest g g) (-I / 2))) / 2

/-- The pole node `w = e^{ℓ/2}`. -/
def poleNode : ℂ := ((Real.exp (ℓ / 2) : ℝ) : ℂ)

theorem poleNode_ne_zero : poleNode ℓ ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'

theorem towerPole_apply (n : Multiplicative ℤ) :
    towerPole g ℓ n = paperFT (EF.weilTest g g) (I / 2) * poleNode ℓ ^ (Multiplicative.toAdd n) +
      paperFT (EF.weilTest g g) (-I / 2) * (poleNode ℓ)⁻¹ ^ (Multiplicative.toAdd n) := by
  set m : ℤ := Multiplicative.toAdd n
  have h1 : cexp (I * (I / 2) * ((-(m : ℝ) * ℓ : ℝ) : ℂ)) = poleNode ℓ ^ m := by
    rw [poleNode, Complex.ofReal_exp, ← Complex.exp_int_mul]
    congr 1
    push_cast
    linear_combination (-(m : ℂ) * ℓ / 2) * Complex.I_sq
  have h2 : cexp (I * (-I / 2) * ((-(m : ℝ) * ℓ : ℝ) : ℂ)) = (poleNode ℓ)⁻¹ ^ m := by
    rw [poleNode, Complex.ofReal_exp, ← Complex.exp_neg, ← Complex.exp_int_mul]
    congr 1
    push_cast
    linear_combination ((m : ℂ) * ℓ / 2) * Complex.I_sq
  rw [towerPole, RHTower.WeilSpectral.polePart, paperFT_translate, paperFT_translate, h1, h2]
  ring

/-- **The pole constituent is one hyperbolic plane.** -/
theorem hermQuad_gram_towerPole {ι : Type*} [Fintype ι] (x : ι → Multiplicative ℤ) (c : ι → ℂ) :
    hermQuad (gram (towerPole g ℓ) x) c =
      hermQuad (gram (pairKernel (valChar (poleNode ℓ)) (poleWeight g)) x) c := by
  set A := paperFT (EF.weilTest g g) (I / 2)
  set B := paperFT (EF.weilTest g g) (-I / 2)
  set w := poleNode ℓ
  have hw : w ≠ 0 := poleNode_ne_zero ℓ
  have hwr : conj w = w := Complex.conj_ofReal _
  have hval : ∀ n, valChar w n = w ^ Multiplicative.toAdd n := fun n => by
    simp [valChar, hw]
  have hrefl : ∀ n, reflectChar (valChar w) n = w⁻¹ ^ Multiplicative.toAdd n := fun n => by
    rw [reflectChar_valChar hw, hwr]
    simp [valChar, hw]
  rw [hermQuad_gram_pairKernel, hermQuad_gram]
  -- both sides through `E(c) = Σ c_a w^{n_a}` and `F(c) = Σ c_a w^{−n_a}`
  set n : ι → ℤ := fun a => Multiplicative.toAdd (x a)
  set E := ∑ a, c a * w ^ n a
  set F := ∑ a, c a * w⁻¹ ^ n a
  have hE : charEval (valChar w) x c = E := by simp only [charEval_apply, hval, E, n]
  have hF : charEval (reflectChar (valChar w)) x c = F := by simp only [charEval_apply, hrefl, F, n]
  have hcF : conj F = ∑ a, conj (c a) * w⁻¹ ^ n a := by
    simp only [F, map_sum, map_mul, map_zpow₀, map_inv₀, hwr]
  have hcE : conj E = ∑ a, conj (c a) * w ^ n a := by
    simp only [E, map_sum, map_mul, map_zpow₀, hwr]
  have hsum : ∑ a, ∑ b, conj (c a) * towerPole g ℓ ((x a)⁻¹ * x b) * c b =
      A * (E * conj F) + B * (F * conj E) := by
    rw [hcF, hcE, sum_mul_sum, sum_mul_sum, Finset.sum_comm (f := fun i j => c i * w ^ n i *
      (conj (c j) * w⁻¹ ^ n j)), Finset.sum_comm (f := fun i j => c i * w⁻¹ ^ n i *
      (conj (c j) * w ^ n j)), mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [towerPole_apply, toAdd_mul, toAdd_inv]
    change conj (c a) * (A * w ^ (-n a + n b) + B * w⁻¹ ^ (-n a + n b)) * c b = _
    simp only [zpow_add₀ hw, zpow_add₀ (inv_ne_zero hw), zpow_neg, inv_zpow, inv_inv]
    ring
  have hre : (A * (E * conj F) + B * (F * conj E)).re =
      (((2 : ℝ) : ℂ) * (poleWeight g * E * conj F)).re := by
    rw [Complex.add_re, ← Complex.conj_re (B * (F * conj E)), ← Complex.add_re]
    congr 1
    simp only [poleWeight, map_mul, conj_conj, A, B]
    push_cast
    ring
  rw [hsum, hE, hF, hre, Complex.re_ofReal_mul]

/-- The pole constituent has at most one negative square. -/
theorem negIndex_towerPole_le_one : negIndex (towerPole g ℓ) ≤ 1 := by
  rw [negIndex_le_iff]
  intro n x
  refine Nat.cast_le.mpr ((ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker _
    (fun _ : Fin 1 => charEval (valChar (poleNode ℓ)) x) fun c hc => ?_).trans (by simp))
  rw [hermQuad_gram_towerPole, hermQuad_gram_pairKernel, hc 0]
  simp

/-- The pole constituent vanishes on the pole hyperplane `Σ c_a w^{n_a} = 0`. -/
theorem hermQuad_gram_towerPole_eq_zero {ι : Type*} [Fintype ι] (x : ι → Multiplicative ℤ)
    {c : ι → ℂ} (hc : charEval (valChar (poleNode ℓ)) x c = 0) :
    hermQuad (gram (towerPole g ℓ) x) c = 0 := by
  rw [hermQuad_gram_towerPole, hermQuad_gram_pairKernel, hc]
  simp

/-- The archimedean-minus-prime constituent of the tower kernel. -/
def towerArchPrime : Multiplicative ℤ → ℂ := fun n => towerArch g ℓ n - towerPrime lam g ℓ n

theorem hermQuad_gram_towerKernel_eq {ι : Type*} [Fintype ι] (x : ι → Multiplicative ℤ)
    (c : ι → ℂ) : hermQuad (gram (towerKernel lam g ℓ) x) c =
      hermQuad (gram (towerPole g ℓ) x) c + hermQuad (gram (towerArchPrime lam g ℓ) x) c := by
  rw [← hermQuad_gram_add]
  congr 2
  funext n
  rw [towerKernel_eq_parts, towerArchPrime]
  ring

/-- **The pole costs at most one square**: the tower index exceeds the index of `Arch − Prime` by
at most one. -/
theorem negIndex_towerKernel_le_archPrime_add_one :
    negIndex (towerKernel lam g ℓ) ≤ negIndex (towerArchPrime lam g ℓ) + 1 := by
  rw [negIndex_le_iff]
  intro n x
  have h := hermNegIndex_le_add_one_of_eq_on_ker (gram (towerKernel lam g ℓ) x)
    (gram (towerArchPrime lam g ℓ) x) (charEval (valChar (poleNode ℓ)) x) fun c hc => by
      rw [hermQuad_gram_towerKernel_eq, hermQuad_gram_towerPole_eq_zero g ℓ x hc, zero_add]
  calc (hermNegIndex (gram (towerKernel lam g ℓ) x) : ℕ∞)
      ≤ (hermNegIndex (gram (towerArchPrime lam g ℓ) x) : ℕ∞) + 1 := by exact_mod_cast h
    _ ≤ negIndex (towerArchPrime lam g ℓ) + 1 := by
        gcongr; exact hermNegIndex_gram_le_negIndex _ x

/-- **Removing the pole costs at most one square** in the other direction. -/
theorem negIndex_archPrime_le_towerKernel_add_one :
    negIndex (towerArchPrime lam g ℓ) ≤ negIndex (towerKernel lam g ℓ) + 1 := by
  rw [negIndex_le_iff]
  intro n x
  have h := hermNegIndex_le_add_one_of_eq_on_ker (gram (towerArchPrime lam g ℓ) x)
    (gram (towerKernel lam g ℓ) x) (charEval (valChar (poleNode ℓ)) x) fun c hc => by
      rw [hermQuad_gram_towerKernel_eq, hermQuad_gram_towerPole_eq_zero g ℓ x hc, zero_add]
  calc (hermNegIndex (gram (towerArchPrime lam g ℓ) x) : ℕ∞)
      ≤ (hermNegIndex (gram (towerKernel lam g ℓ) x) : ℕ∞) + 1 := by exact_mod_cast h
    _ ≤ negIndex (towerKernel lam g ℓ) + 1 := by
        gcongr; exact hermNegIndex_gram_le_negIndex _ x

end GaloisForLFunctions.HeckeKreinToeplitz
