import GaloisForLFunctions.AdelicKreinGeometry.PrimeTowersGlueAtFullIndex
import GaloisForLFunctions.AdelicKreinGeometry.TheSignatureOfASeparableAssembly

/-!
# A signature formula for prime towers

Local data on finitely many prime towers, assembled on `ℚ_{>0}` and glued at the archimedean place:

  `K(u) = Σ_{p ∈ S} k_p(v_p(u))`  (`towerAssembly`),   `Φ = K(|a|) − c|a|^{−1/2}|b|`.

* **The tower coordinates are free** (`valS_surjective`): `u ↦ (v_p(u))_{p ∈ S}` maps `ℚ_{>0}` onto
  `ℤ^S`, so `κ(K) = κ(Σ_p k_p(g_p))` (`negIndex_towerAssembly`).
* **The glue is free** (`towerAssembly_periodic`): a prime `q ∉ S` leaves every `v_p` unchanged, so `K` is
  periodic under `q` and the boost hyperplane costs nothing.
* **The signature formula** (`towerSignature_lower`, `towerSignature_upper`):

    `Σ_{p ∈ S} κ₀(k_p) + 1 ≤ κ(Φ) ≤ Σ_{p ∈ S} κ₀(k_p) + 2`,

  the local defects `κ₀(k_p)` (the polar indices of the local kernels), one archimedean gluing square,
  and at most one square for the shared pole of the assembly.

So for finitely many towers the global index is computed from local data: each prime contributes its
polar index, the archimedean place contributes exactly one square, and the only remaining ambiguity
is the single square of the common constant direction.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable (S : Finset Nat.Primes)

instance (p : S) : Fact ((p : Nat.Primes) : ℕ).Prime := ⟨(p : Nat.Primes).2⟩

/-- The tower coordinates `u ↦ (v_p(u))_{p ∈ S}`. -/
def valS : posUnits →* (S → Multiplicative ℤ) :=
  MonoidHom.pi fun p => towerVal ((p : Nat.Primes) : ℕ)

theorem valS_apply (u : posUnits) (p : S) :
    valS S u p = Multiplicative.ofAdd (padicValRat ((p : Nat.Primes) : ℕ) (((u : ℚˣ) : ℚ))) := rfl

/-- `v_q(p) = [p = q]` for primes. -/
theorem towerVal_primePos (p q : Nat.Primes) :
    @towerVal (q : ℕ) ⟨q.2⟩ (@primePos (p : ℕ) ⟨p.2⟩) =
      Multiplicative.ofAdd (if p = q then 1 else 0) := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  simp only [towerVal, primePos, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    ratPadicValHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, padicValRat.of_nat]
  split_ifs with h
  · subst h; rw [padicValNat.self p.2.one_lt]; rfl
  · rw [padicValNat_primes (fun e => h (Subtype.ext e).symm)]; rfl

/-- **The tower coordinates are free.** -/
theorem valS_surjective : Function.Surjective (valS S) := fun e => by
  classical
  refine ⟨∏ p : S, (@primePos ((p : Nat.Primes) : ℕ) ⟨(p : Nat.Primes).2⟩) ^
    Multiplicative.toAdd (e p), ?_⟩
  funext q
  change towerVal ((q : Nat.Primes) : ℕ) _ = e q
  rw [map_prod, Finset.prod_eq_single q]
  · rw [map_zpow, towerVal_primePos, if_pos rfl, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
  · intro p _ hpq
    rw [map_zpow, towerVal_primePos, if_neg (fun h => hpq (Subtype.ext h)), ofAdd_zero, one_zpow]
  · intro h; exact absurd (mem_univ q) h

/-- The assembly of local kernels on finitely many prime towers, `K(u) = Σ_{p ∈ S} k_p(v_p(u))`. -/
def towerAssembly (k : S → Multiplicative ℤ → ℂ) : posUnits → ℂ :=
  separable (H := fun _ => Multiplicative ℤ) k ∘ valS S

theorem negIndex_towerAssembly (k : S → Multiplicative ℤ → ℂ) :
    negIndex (towerAssembly S k) = negIndex (separable (H := fun _ => Multiplicative ℤ) k) :=
  negIndex_comp_of_surjective _ _ (valS_surjective S)

theorem isHermKernel_towerAssembly {k : S → Multiplicative ℤ → ℂ} (hk : ∀ p, IsHermKernel (k p)) :
    IsHermKernel (towerAssembly S k) := by
  have h : IsHermKernel (separable (H := fun _ => Multiplicative ℤ) k) := fun g => by
    simp only [separable, Pi.inv_apply, map_sum]
    exact Finset.sum_congr rfl fun p _ => hk p (g p)
  exact h.comp _

/-- **The glue is free**: a prime outside `S` leaves every tower coordinate unchanged. -/
theorem towerAssembly_periodic (k : S → Multiplicative ℤ → ℂ) :
    ∃ v₀ : posUnits, v₀ ≠ 1 ∧ ∀ u, towerAssembly S k (v₀ * u) = towerAssembly S k u := by
  classical
  obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (S.sup (fun p => (p : ℕ)) + 1)
  have hqS : (⟨q, hq⟩ : Nat.Primes) ∉ S := fun h => by
    have := Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) h
    simp only at this
    omega
  haveI : Fact q.Prime := ⟨hq⟩
  refine ⟨primePos q, fun h => ?_, fun u => ?_⟩
  · have := congrArg (fun v : posUnits => (((v : ℚˣ) : ℚ))) h
    simp only [primePos, Units.val_mk0, OneMemClass.coe_one, Units.val_one] at this
    exact hq.one_lt.ne' (by exact_mod_cast this)
  · have hv : valS S (primePos q) = 1 := by
      funext p
      change towerVal ((p : Nat.Primes) : ℕ) (primePos q) = 1
      have h := towerVal_primePos ⟨q, hq⟩ (p : Nat.Primes)
      have hne : ¬ ((⟨q, hq⟩ : Nat.Primes) = (p : Nat.Primes)) := fun e => hqS (by rw [e]; exact p.2)
      split_ifs at h with h'
      · exact absurd h' hne
      · rw [h, ofAdd_zero]
    simp only [towerAssembly, Function.comp_apply, map_mul, hv, one_mul]

theorem negIndex_archGlue_towerAssembly {k : S → Multiplicative ℤ → ℂ}
    (hk : ∀ p, IsHermKernel (k p)) {c : ℝ} (hc : 0 < c) :
    negIndex (archGlue (towerAssembly S k) c) =
      negIndex (separable (H := fun _ => Multiplicative ℤ) k) + 1 := by
  obtain ⟨v₀, hv₀, hper⟩ := towerAssembly_periodic S k
  rw [negIndex_archGlue_eq_of_periodic (isHermKernel_towerAssembly S hk) hv₀ hper hc,
    negIndex_towerAssembly]

/-- **The signature formula, lower bound**: the local defects and the archimedean square. -/
theorem towerSignature_lower {k : S → Multiplicative ℤ → ℂ} (hk : ∀ p, IsHermKernel (k p)) {c : ℝ}
    (hc : 0 < c) :
    ∑ p, polarIndex (k p) + 1 ≤ negIndex (archGlue (towerAssembly S k) c) := by
  rw [negIndex_archGlue_towerAssembly S hk hc]
  exact add_le_add (polarIndex_sum_le_negIndex_separable (H := fun _ => Multiplicative ℤ) k) le_rfl

/-- **The signature formula, upper bound**: at most one more square, for the shared pole. -/
theorem towerSignature_upper {k : S → Multiplicative ℤ → ℂ} (hk : ∀ p, IsHermKernel (k p)) {c : ℝ}
    (hc : 0 < c) :
    negIndex (archGlue (towerAssembly S k) c) ≤ ∑ p, polarIndex (k p) + 2 := by
  rw [negIndex_archGlue_towerAssembly S hk hc, show (2 : ℕ∞) = 1 + 1 from rfl, ← add_assoc]
  exact add_le_add (negIndex_separable_le_polarIndex_sum_add_one (H := fun _ => Multiplicative ℤ) k hk)
    le_rfl

end GaloisForLFunctions.AdelicKreinGeometry

#print axioms GaloisForLFunctions.AdelicKreinGeometry.towerSignature_lower
#print axioms GaloisForLFunctions.AdelicKreinGeometry.towerSignature_upper
