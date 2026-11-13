import GaloisForLFunctions.RHTower.Artin.EveryArtinEulerProductIsAProductOfHeckeLSeries
import GaloisForLFunctions.RHTower.Artin.ALinearCharacterWithTrivialArtinSymbolsAtAlmostAllPrimesIsTrivial
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheOrdersOfARayClassLFunctionAreTheMultiplicitiesOfItsConfiguration
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheIndexOfAnIntegerCombinationOfConfigurationsCountsItsNetMultiplicities

/-!
# The orders of an Artin `L`-function are the net multiplicities of its virtual configuration

Let `L/K` be a Galois extension of number fields with group `G` and `ρ` a representation of `G`.
By Brauer's theorem and the reciprocity law, for `Re s > 1`

  `L(s, ρ, L/K) = Π_q Λ_q(s)^{n_q}`,  `Λ_q(s) = L(s, ψ_q) · Π_{v | c_q} (1 − (χ_q, v) N v^{−s})^{−1}`,

with integers `n_q` and ray class characters `ψ_q` of fixed fields. Let `Z_q` be the
configuration of `ψ_q`. The virtual configuration of `ρ` is the integer combination
`Σ_q n_q Z_q`, with net multiplicity `m(w) = Σ_q n_q m_{Z_q}(w)`.

**Theorem** (`exists_virtualConfig_artin`). Write the `L`-function as a quotient `A / B` of
functions analytic on `Re s > 0`, `B ≢ 0`: `A = B · L(·, ρ, L/K)` on `Re s > 1`. Then

* `ord_w A − ord_w B = m(w)` at every `w ≠ 1` with `Re w > 0`;
* `ord_1 A − ord_1 B = −Σ_{q : ψ_q = 1} n_q`;
* the form `Σ_q n_q W_{Z_q}` has `m` negative squares on some family of `m` tests iff at least
  `m` points are zeros or poles of `A / B` right of the critical line, other than `1`, or poles
  on the line.

No continuation of the `L`-function is assumed beyond the quotient `A / B` on `Re s > 0`.

Proof. `G_q = (s − 1) Λ_q` is analytic on `Re s > 0`, with
`ord_w G_q = m_{Z_q}(w) + [w = 1][ψ_q ≠ 1]`, and `1` is no point of `Z_q`. On `Re s > 1`,
`A (s − 1)^a Π_{n_q < 0} G_q^{−n_q} = B (s − 1)^b Π_{n_q > 0} G_q^{n_q}` with
`a − b = Σ_q n_q`; the half plane is connected, so the identity holds on it, and orders add.
-/

noncomputable section

open Complex Filter Topology Set NumberField
open scoped Classical

universe u

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HeckeLFunctions HTGeometry IsDedekindDomain Zeta23 ArithmeticCastelnuovoSeveri

/-! ### Orders of products of integer powers -/

/-- The order of a finite product is the sum of the orders. -/
theorem analyticOrderAt_finset_prod {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ) {z : ℂ}
    (hf : ∀ i ∈ S, AnalyticAt ℂ (f i) z) :
    analyticOrderAt (fun s => ∏ i ∈ S, f i s) z = ∑ i ∈ S, analyticOrderAt (f i) z := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact (analyticAt_const (v := (1 : ℂ))).analyticOrderAt_eq_zero.mpr one_ne_zero
  | insert a S ha ih =>
    have hS : ∀ i ∈ S, AnalyticAt ℂ (f i) z := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h := analyticOrderAt_fun_mul (hf a (Finset.mem_insert_self a S))
      (Finset.analyticAt_fun_prod S hS)
    rw [Finset.sum_insert ha, ← ih hS, ← h]
    exact congrArg (fun g => analyticOrderAt g z) (funext fun s => Finset.prod_insert ha)

/-- A product of integer powers of a fixed element `≠ 0`. -/
theorem prod_zpow_eq_zpow_sum {ι : Type*} {x : ℂ} (hx : x ≠ 0) (S : Finset ι) (e : ι → ℤ) :
    ∏ i ∈ S, x ^ e i = x ^ ∑ i ∈ S, e i := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

/-- The order of `f(s) (s − 1)^a`. -/
theorem analyticOrderAt_mul_sub_one_pow {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (a : ℕ) :
    analyticOrderAt (fun s => f s * (s - 1) ^ a) z =
      analyticOrderAt f z + ((a * if z = 1 then 1 else 0 : ℕ) : ℕ∞) := by
  have hsub : AnalyticAt ℂ (fun s : ℂ => s - 1) z := analyticAt_id.sub analyticAt_const
  have hp : AnalyticAt ℂ (fun s : ℂ => (s - 1) ^ a) z := hsub.pow a
  have hpow : analyticOrderAt (fun s : ℂ => (s - 1) ^ a) z =
      a • analyticOrderAt (fun s : ℂ => s - 1) z := analyticOrderAt_pow hsub a
  rw [analyticOrderAt_fun_mul hf hp, hpow, analyticOrderAt_sub_one]
  congr 1
  split_ifs <;> simp

/-- **Orders of a product of integer powers.** Let `A`, `B`, `G_q` be analytic on a connected
open set `U`, `B ≢ 0`, the `G_q` without zeros on an open set `V ⊆ U`, and
`A = B Π_q G_q^{n_q}` on `V`. Then at every point of `U` the orders are finite and
`ord A − ord B = Σ_q n_q ord G_q`. -/
theorem analyticOrderNatAt_sub_eq_sum_of_eq_mul_prod_zpow {ι : Type*} {U V : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hV : IsOpen V) (hVU : V ⊆ U) (hVne : V.Nonempty)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A U) (hB : DifferentiableOn ℂ B U)
    (hB0 : ∃ u ∈ U, analyticOrderAt B u ≠ ⊤) (G : ι → ℂ → ℂ)
    (hG : ∀ q, DifferentiableOn ℂ (G q) U) (hG0 : ∀ q, ∀ s ∈ V, G q s ≠ 0) (n : ι →₀ ℤ)
    (hAB : ∀ s ∈ V, A s = B s * n.prod fun q k => G q s ^ k) {z : ℂ} (hz : z ∈ U) :
    analyticOrderAt A z ≠ ⊤ ∧ analyticOrderAt B z ≠ ⊤ ∧
    (analyticOrderNatAt A z : ℤ) - analyticOrderNatAt B z =
      n.sum fun q k => k * (analyticOrderNatAt (G q) z : ℤ) := by
  obtain ⟨v, hv⟩ := hVne
  have hAan := hA.analyticOnNhd hU
  have hBan := hB.analyticOnNhd hU
  have hGan : ∀ q, AnalyticOnNhd ℂ (G q) U := fun q => (hG q).analyticOnNhd hU
  have hconn : IsConnected U := ⟨⟨v, hVU hv⟩, hUc⟩
  -- the identity with the negative powers on the left
  have hL : DifferentiableOn ℂ
      (fun s => A s * ∏ q ∈ n.support, G q s ^ (-(n q)).toNat) U :=
    hA.mul (DifferentiableOn.fun_finsetProd fun q _ => (hG q).pow _)
  have hR : DifferentiableOn ℂ
      (fun s => B s * ∏ q ∈ n.support, G q s ^ (n q).toNat) U :=
    hB.mul (DifferentiableOn.fun_finsetProd fun q _ => (hG q).pow _)
  have hV' : ∀ s ∈ V, A s * ∏ q ∈ n.support, G q s ^ (-(n q)).toNat =
      B s * ∏ q ∈ n.support, G q s ^ (n q).toNat := by
    intro s hs
    rw [hAB s hs, Finsupp.prod, mul_assoc, ← Finset.prod_mul_distrib]
    refine congrArg (B s * ·) (Finset.prod_congr rfl fun q _ => ?_)
    have hne := hG0 q s hs
    rw [← zpow_natCast (G q s) (-(n q)).toNat, ← zpow_natCast (G q s) (n q).toNat,
      ← zpow_add₀ hne]
    congr 1
    omega
  have heq : EqOn (fun s => A s * ∏ q ∈ n.support, G q s ^ (-(n q)).toNat)
      (fun s => B s * ∏ q ∈ n.support, G q s ^ (n q).toNat) U :=
    (hL.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hR.analyticOnNhd hU) hUc
      (hVU hv) (Filter.eventuallyEq_of_mem (hV.mem_nhds hv) hV')
  -- orders add
  have hord := analyticOrderAt_congr (heq.eventuallyEq_of_mem (hU.mem_nhds hz))
  have hGz : ∀ q, AnalyticAt ℂ (G q) z := fun q => hGan q z hz
  have hpow : ∀ (e : ι → ℕ), analyticOrderAt (fun s => ∏ q ∈ n.support, G q s ^ e q) z =
      ∑ q ∈ n.support, e q • analyticOrderAt (G q) z := fun e => by
    rw [analyticOrderAt_finset_prod n.support (fun q s => G q s ^ e q)
      (fun q _ => (hGz q).pow _)]
    exact Finset.sum_congr rfl fun q _ => analyticOrderAt_pow (hGz q) (e q)
  have hmulL := analyticOrderAt_fun_mul (hAan z hz)
    (Finset.analyticAt_fun_prod n.support fun q _ => (hGz q).pow (-(n q)).toNat)
  have hmulR := analyticOrderAt_fun_mul (hBan z hz)
    (Finset.analyticAt_fun_prod n.support fun q _ => (hGz q).pow (n q).toNat)
  have hord' : analyticOrderAt A z + ∑ q ∈ n.support, (-(n q)).toNat • analyticOrderAt (G q) z =
      analyticOrderAt B z + ∑ q ∈ n.support, (n q).toNat • analyticOrderAt (G q) z := by
    rw [← hpow, ← hpow]
    exact hmulL.symm.trans (hord.trans hmulR)
  -- the orders are finite
  have hBtop : analyticOrderAt B z ≠ ⊤ := by
    obtain ⟨u, hu, hBu⟩ := hB0
    exact (hBan.exists_analyticOrderAt_ne_top_iff_forall hconn).mp ⟨⟨u, hu⟩, hBu⟩ ⟨z, hz⟩
  have hGtop : ∀ q, analyticOrderAt (G q) z ≠ ⊤ := fun q =>
    ((hGan q).exists_analyticOrderAt_ne_top_iff_forall hconn).mp
      ⟨⟨v, hVU hv⟩, by
        rw [((hGan q) v (hVU hv)).analyticOrderAt_eq_zero.mpr (hG0 q v hv)]
        exact ENat.zero_ne_top⟩ ⟨z, hz⟩
  have hGcast : ∀ q, analyticOrderAt (G q) z = (analyticOrderNatAt (G q) z : ℕ∞) := fun q =>
    (Nat.cast_analyticOrderNatAt (hGtop q)).symm
  have hBcast := (Nat.cast_analyticOrderNatAt hBtop).symm
  have hsum : ∀ e : ι → ℕ, ∑ q ∈ n.support, e q • analyticOrderAt (G q) z =
      ((∑ q ∈ n.support, e q * analyticOrderNatAt (G q) z : ℕ) : ℕ∞) := fun e => by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [hGcast q, nsmul_eq_mul, Nat.cast_mul]
  rw [hsum, hsum, hBcast, ← Nat.cast_add] at hord'
  have hAtop : analyticOrderAt A z ≠ ⊤ := fun h => by
    rw [h, top_add] at hord'
    exact ENat.coe_ne_top _ hord'.symm
  refine ⟨hAtop, hBtop, ?_⟩
  rw [← Nat.cast_analyticOrderNatAt hAtop, ← Nat.cast_add, Nat.cast_inj] at hord'
  have hZ : (analyticOrderNatAt A z : ℤ) +
      ∑ q ∈ n.support, ((-(n q)).toNat : ℤ) * (analyticOrderNatAt (G q) z : ℤ) =
      (analyticOrderNatAt B z : ℤ) +
      ∑ q ∈ n.support, ((n q).toNat : ℤ) * (analyticOrderNatAt (G q) z : ℤ) := by
    exact_mod_cast hord'
  have hsplit : n.sum (fun q k => k * (analyticOrderNatAt (G q) z : ℤ)) =
      ∑ q ∈ n.support, ((n q).toNat : ℤ) * (analyticOrderNatAt (G q) z : ℤ) -
      ∑ q ∈ n.support, ((-(n q)).toNat : ℤ) * (analyticOrderNatAt (G q) z : ℤ) := by
    rw [Finsupp.sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← sub_mul]
    congr 1
    omega
  rw [hsplit]
  linarith

/-- **Orders of a product of integer powers of functions with a pole at `1`.** Let `A`, `B` be
analytic on `Re s > 0`, `B ≢ 0`, and `A = B Π_q Λ_q^{n_q}` on `Re s > 1`, where the `Λ_q` have
no zeros there and `G_q = (s − 1) Λ_q` continue analytically to `Re s > 0`. Then for
`Re z > 0`: `ord_z A − ord_z B = Σ_q n_q ord_z G_q − [z = 1] Σ_q n_q`. -/
theorem analyticOrderNatAt_sub_eq_sum_sub_of_cleared {ι : Type*}
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A {s : ℂ | 0 < s.re})
    (hB : DifferentiableOn ℂ B {s : ℂ | 0 < s.re}) (hB0 : ∃ u : ℂ, 0 < u.re ∧ B u ≠ 0)
    (G Λ : ι → ℂ → ℂ) (hG : ∀ q, DifferentiableOn ℂ (G q) {s : ℂ | 0 < s.re})
    (hGΛ : ∀ q, ∀ s : ℂ, 1 < s.re → G q s = (s - 1) * Λ q s)
    (hΛ0 : ∀ q, ∀ s : ℂ, 1 < s.re → Λ q s ≠ 0) (n : ι →₀ ℤ)
    (hAB : ∀ s : ℂ, 1 < s.re → A s = B s * n.prod fun q k => Λ q s ^ k) {z : ℂ}
    (hz : 0 < z.re) :
    (analyticOrderNatAt A z : ℤ) - analyticOrderNatAt B z =
      (n.sum fun q k => k * (analyticOrderNatAt (G q) z : ℤ)) -
        (∑ q ∈ n.support, n q) * (if z = 1 then 1 else 0) := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected {s : ℂ | 0 < s.re} :=
    (convex_halfSpace_gt ⟨fun _ _ => rfl, fun a z => by simp⟩ _).isPreconnected
  have hV : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hVU : {s : ℂ | 1 < s.re} ⊆ {s : ℂ | 0 < s.re} := fun s (hs : 1 < s.re) =>
    show 0 < s.re by linarith
  have hVne : ({s : ℂ | 1 < s.re}).Nonempty := ⟨2, show (1 : ℝ) < (2 : ℂ).re by norm_num⟩
  have hsubpow : ∀ a : ℕ, Differentiable ℂ fun s : ℂ => (s - 1) ^ a := fun a =>
    (differentiable_id.sub_const 1).pow a
  have hab : ((∑ q ∈ n.support, (n q).toNat : ℕ) : ℤ) =
      ((∑ q ∈ n.support, (-(n q)).toNat : ℕ) : ℤ) + ∑ q ∈ n.support, n q := by
    rw [Nat.cast_sum, Nat.cast_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by omega
  -- the identity with the poles cleared
  have hV' : ∀ s ∈ {s : ℂ | 1 < s.re},
      A s * (s - 1) ^ (∑ q ∈ n.support, (n q).toNat) =
        B s * (s - 1) ^ (∑ q ∈ n.support, (-(n q)).toNat) *
          n.prod fun q k => G q s ^ k := by
    intro s hs
    have hs' : (1 : ℝ) < s.re := hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_one_lt_re hs')
    have hprodG : (n.prod fun q k => G q s ^ k) =
        (s - 1) ^ (∑ q ∈ n.support, n q) * n.prod fun q k => Λ q s ^ k := by
      rw [Finsupp.prod, Finsupp.prod, ← prod_zpow_eq_zpow_sum hs1, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun q _ => by rw [hGΛ q s hs', mul_zpow]
    rw [hprodG, hAB s hs', ← zpow_natCast (s - 1) (∑ q ∈ n.support, (n q).toNat),
      ← zpow_natCast (s - 1) (∑ q ∈ n.support, (-(n q)).toNat), hab, zpow_add₀ hs1]
    ring
  have hG0 : ∀ q, ∀ s ∈ {s : ℂ | 1 < s.re}, G q s ≠ 0 := fun q s hs => by
    have hs' : (1 : ℝ) < s.re := hs
    rw [hGΛ q s hs']
    exact mul_ne_zero (sub_ne_zero.mpr (ne_one_of_one_lt_re hs')) (hΛ0 q s hs')
  obtain ⟨u, hu, hBu⟩ := hB0
  have hBu' : analyticOrderAt
      (fun s => B s * (s - 1) ^ (∑ q ∈ n.support, (-(n q)).toNat)) u ≠ ⊤ := by
    have hBan : AnalyticAt ℂ B u := hB.analyticAt (hU.mem_nhds hu)
    rw [analyticOrderAt_mul_sub_one_pow hBan, hBan.analyticOrderAt_eq_zero.mpr hBu, zero_add]
    exact ENat.coe_ne_top _
  obtain ⟨hA1, hB1, hgen⟩ := analyticOrderNatAt_sub_eq_sum_of_eq_mul_prod_zpow hU hUc hV hVU
    hVne (A := fun s => A s * (s - 1) ^ (∑ q ∈ n.support, (n q).toNat))
    (B := fun s => B s * (s - 1) ^ (∑ q ∈ n.support, (-(n q)).toNat))
    (hA.mul (hsubpow _).differentiableOn) (hB.mul (hsubpow _).differentiableOn)
    ⟨u, hu, hBu'⟩ G hG hG0 n hV' hz
  have hAz : AnalyticAt ℂ A z := hA.analyticAt (hU.mem_nhds hz)
  have hBz : AnalyticAt ℂ B z := hB.analyticAt (hU.mem_nhds hz)
  rw [analyticOrderAt_mul_sub_one_pow hAz] at hA1
  rw [analyticOrderAt_mul_sub_one_pow hBz] at hB1
  have hAtop : analyticOrderAt A z ≠ ⊤ := fun h => hA1 (by rw [h, top_add])
  have hBtop : analyticOrderAt B z ≠ ⊤ := fun h => hB1 (by rw [h, top_add])
  have hnat : ∀ {f : ℂ → ℂ} (a : ℕ), AnalyticAt ℂ f z → analyticOrderAt f z ≠ ⊤ →
      analyticOrderNatAt (fun s => f s * (s - 1) ^ a) z =
        analyticOrderNatAt f z + a * if z = 1 then 1 else 0 := fun {f} a hf htop => by
    have h := analyticOrderAt_mul_sub_one_pow hf a (z := z)
    rw [← Nat.cast_analyticOrderNatAt htop, ← Nat.cast_add] at h
    rw [analyticOrderNatAt, h]
    rfl
  rw [hnat _ hAz hAtop, hnat _ hBz hBtop] at hgen
  rw [← hgen]
  by_cases h1 : z = 1
  · rw [if_pos h1, if_pos h1, mul_one, mul_one, mul_one, Nat.cast_add, Nat.cast_add, hab]
    ring
  · simp only [if_neg h1, mul_zero, add_zero, sub_zero]

/-- A point outside a configuration has multiplicity zero. -/
theorem extMult_of_notMem {Z : ZeroConfig} {ρ : ℂ} (h : ρ ∉ Z.carrier) : extMult Z ρ = 0 :=
  if_neg h

/-- **Orders through configurations.** In the situation of
`analyticOrderNatAt_sub_eq_sum_sub_of_cleared`, let `ord_z G_q = m_{Z_q}(z) + [z = 1](1 − p_q)`
for configurations `Z_q` without the point `1`. Then `ord_z A − ord_z B` is the net
multiplicity of `Σ_q n_q Z_q` at `z ≠ 1`, and `−Σ_q n_q p_q` at `z = 1`. -/
theorem analyticOrderNatAt_sub_of_configurations {ι : Type*} (n : ι →₀ ℤ) (Z : ι → ZeroConfig)
    (p : ι → ℤ) (Λ G : ι → ℂ → ℂ) (hG : ∀ q, DifferentiableOn ℂ (G q) {s : ℂ | 0 < s.re})
    (hGΛ : ∀ q, ∀ s : ℂ, 1 < s.re → G q s = (s - 1) * Λ q s)
    (hΛ0 : ∀ q, ∀ s : ℂ, 1 < s.re → Λ q s ≠ 0)
    (hord : ∀ q, ∀ z : ℂ, 0 < z.re → (analyticOrderNatAt (G q) z : ℤ) =
      extMult (Z q) z + if z = 1 then 1 - p q else 0)
    (h1 : ∀ q, (1 : ℂ) ∉ (Z q).carrier) {A B : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A {s : ℂ | 0 < s.re})
    (hB : DifferentiableOn ℂ B {s : ℂ | 0 < s.re}) (hB0 : ∃ u : ℂ, 0 < u.re ∧ B u ≠ 0)
    (hAB : ∀ s : ℂ, 1 < s.re → A s = B s * n.prod fun q k => Λ q s ^ k) {z : ℂ}
    (hz : 0 < z.re) :
    (analyticOrderNatAt A z : ℤ) - analyticOrderNatAt B z =
      if z = 1 then -(n.sum fun q k => k * p q) else netMult n Z z := by
  rw [analyticOrderNatAt_sub_eq_sum_sub_of_cleared hA hB hB0 G Λ hG hGΛ hΛ0 n hAB hz]
  by_cases h : z = 1
  · subst h
    rw [if_pos rfl, if_pos rfl, mul_one, Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hord q 1 hz, if_pos rfl, extMult_of_notMem (h1 q), Nat.cast_zero]
    ring
  · rw [if_neg h, if_neg h, mul_zero, sub_zero, netMult]
    exact Finsupp.sum_congr fun q _ => by rw [hord q z hz, if_neg h, add_zero]

/-- The defect points of a combination of configurations without the point `1`, through the
orders of a quotient `A / B` with these net multiplicities. -/
theorem combinationDefect_eq_of_orders {ι : Type*} (n : ι →₀ ℤ) (Z : ι → ZeroConfig)
    (h1 : ∀ q, (1 : ℂ) ∉ (Z q).carrier) {A B : ℂ → ℂ}
    (hord : ∀ z : ℂ, 0 < z.re → z ≠ 1 →
      (analyticOrderNatAt A z : ℤ) - analyticOrderNatAt B z = netMult n Z z) :
    combinationDefect n Z =
      {w : ℂ | 1 / 2 < w.re ∧ w ≠ 1 ∧ analyticOrderNatAt A w ≠ analyticOrderNatAt B w} ∪
        {w : ℂ | w.re = 1 / 2 ∧ analyticOrderNatAt A w < analyticOrderNatAt B w} := by
  have hnet1 : netMult n Z 1 = 0 := by
    rw [netMult]
    refine Finset.sum_eq_zero fun q _ => ?_
    show n q * ((extMult (Z q) 1 : ℕ) : ℤ) = 0
    rw [extMult_of_notMem (h1 q), Nat.cast_zero, mul_zero]
  have hhalf : ∀ w : ℂ, w.re = 1 / 2 → w ≠ 1 := by
    rintro w hw rfl
    rw [Complex.one_re] at hw
    norm_num at hw
  ext w
  simp only [combinationDefect, Set.mem_union, Set.mem_setOf_eq]
  refine or_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨hre, hne⟩
    have hw1 : w ≠ 1 := fun h => hne (by rw [h]; exact hnet1)
    refine ⟨hre, hw1, fun h => hne ?_⟩
    rw [← hord w (by linarith) hw1, h, sub_self]
  · rintro ⟨hre, hw1, hne⟩
    refine ⟨hre, fun h => hne ?_⟩
    rw [← hord w (by linarith) hw1, sub_eq_zero] at h
    exact_mod_cast h
  · rintro ⟨hre, hlt⟩
    rw [← hord w (by rw [hre]; norm_num) (hhalf w hre), sub_neg] at hlt
    exact ⟨hre, by exact_mod_cast hlt⟩
  · rintro ⟨hre, hlt⟩
    refine ⟨hre, ?_⟩
    rw [← hord w (by rw [hre]; norm_num) (hhalf w hre), sub_neg]
    exact_mod_cast hlt

/-! ### A ray class `L`-function with finitely many Euler factors -/

section RayClass

variable {F : Type*} [Field F] [NumberField F]

/-- A finite product of Euler factors: `Π_{v ∈ S} (1 − b_v N v^{−s})^{−1}`. -/
def eulerFactorInverse (S : Finset (HeightOneSpectrum (𝓞 F)))
    (b : HeightOneSpectrum (𝓞 F) → ℂ) (s : ℂ) : ℂ :=
  ∏ v ∈ S, (1 - b v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹

theorem eulerFactorInverse_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F)))
    {b : HeightOneSpectrum (𝓞 F) → ℂ} (hb : ∀ v, ‖b v‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) :
    eulerFactorInverse S b s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun v _ =>
    inv_ne_zero (one_sub_mul_absNorm_cpow_ne_zero v (hb v) hs)

theorem differentiableOn_eulerFactorInverse (S : Finset (HeightOneSpectrum (𝓞 F)))
    {b : HeightOneSpectrum (𝓞 F) → ℂ} (hb : ∀ v, ‖b v‖ ≤ 1) :
    DifferentiableOn ℂ (eulerFactorInverse S b) {s : ℂ | 0 < s.re} := by
  show DifferentiableOn ℂ (fun s : ℂ => ∏ v ∈ S,
    (1 - b v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) _
  refine DifferentiableOn.fun_finsetProd fun v _ => ?_
  exact (differentiable_one_sub_mul_absNorm_cpow v (b v)).differentiableOn.inv fun s hs =>
    one_sub_mul_absNorm_cpow_ne_zero v (hb v) hs

/-- Finitely many Euler factors do not change the orders of `E_ψ(s) = (s − 1) L(s, ψ)` in
`Re s > 0`. -/
theorem analyticOrderNatAt_heckePoleCleared_mul_eulerFactorInverse (𝔪 : Modulus F)
    (ψ : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum (𝓞 F)))
    {b : HeightOneSpectrum (𝓞 F) → ℂ} (hb : ∀ v, ‖b v‖ ≤ 1) {z : ℂ} (hz : 0 < z.re) :
    analyticOrderNatAt (fun s => heckePoleCleared 𝔪 ψ s * eulerFactorInverse S b s) z =
      extMult (rayClassZeros 𝔪 ψ) z + if ψ ≠ 1 ∧ z = 1 then 1 else 0 := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hD : AnalyticAt ℂ (eulerFactorInverse S b) z :=
    (differentiableOn_eulerFactorInverse S hb).analyticAt (hU.mem_nhds hz)
  have h : analyticOrderAt (fun s => heckePoleCleared 𝔪 ψ s * eulerFactorInverse S b s) z =
      analyticOrderAt (heckePoleCleared 𝔪 ψ) z := by
    rw [analyticOrderAt_fun_mul ((differentiable_heckePoleCleared 𝔪 ψ).analyticAt z) hD,
      hD.analyticOrderAt_eq_zero.mpr (eulerFactorInverse_ne_zero S hb hz), add_zero]
  rw [← analyticOrderNatAt_heckePoleCleared 𝔪 ψ hz]
  exact congrArg ENat.toNat h

end RayClass

/-! ### The Hecke sides of the Brauer pairs -/

variable (K L : Type u) {G V : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [Group G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The Hecke side of a Brauer pair with its pole cleared: `(s − 1) Λ_q(s)`, analytic on
`Re s > 0`. -/
def brauerHeckeCleared (q : brauerElementaryMonomialIndex G) (c : ℕ) [NeZero c]
    (ψ : HeckeCharacter (normModulus
      (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) c)) (s : ℂ) : ℂ :=
  heckePoleCleared (normModulus
      (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) c) ψ s *
    eulerFactorInverse (finite_primes_dvd (normModulus
        (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) c)).toFinset
      (fun v => artinSymbol (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L)
        L q.2 v) s

theorem differentiableOn_brauerHeckeCleared (q : brauerElementaryMonomialIndex G) (c : ℕ)
    [NeZero c] (ψ : HeckeCharacter (normModulus
      (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) c)) :
    DifferentiableOn ℂ (brauerHeckeCleared K L q c ψ) {s : ℂ | 0 < s.re} :=
  (differentiable_heckePoleCleared _ ψ).differentiableOn.mul
    (differentiableOn_eulerFactorInverse _ (norm_artinSymbol_le_one
      (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) L q.2))

theorem brauerHeckeCleared_eq (q : brauerElementaryMonomialIndex G) (c : ℕ) [NeZero c]
    (ψ : HeckeCharacter (normModulus
      (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) c)) {s : ℂ}
    (hs : 1 < s.re) :
    brauerHeckeCleared K L q c ψ s = (s - 1) * brauerHeckeEulerProduct K L q c ψ s := by
  rw [brauerHeckeCleared, brauerHeckeEulerProduct, heckePoleCleared_eq_heckeL _ ψ hs, mul_assoc]
  rfl

theorem brauerHeckeEulerProduct_ne_zero (q : brauerElementaryMonomialIndex G) (c : ℕ)
    [NeZero c] (ψ : HeckeCharacter (normModulus
      (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) c)) {s : ℂ}
    (hs : 1 < s.re) : brauerHeckeEulerProduct K L q c ψ s ≠ 0 :=
  mul_ne_zero (heckeL_ne_zero _ ψ hs)
    (eulerFactorInverse_ne_zero _ (norm_artinSymbol_le_one
      (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) L q.2)
      (zero_lt_one.trans hs))

theorem analyticOrderNatAt_brauerHeckeCleared (q : brauerElementaryMonomialIndex G) (c : ℕ)
    [NeZero c] (ψ : HeckeCharacter (normModulus
      (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) c)) {z : ℂ}
    (hz : 0 < z.re) :
    analyticOrderNatAt (brauerHeckeCleared K L q c ψ) z =
      extMult (rayClassZeros _ ψ) z + if ψ ≠ 1 ∧ z = 1 then 1 else 0 :=
  analyticOrderNatAt_heckePoleCleared_mul_eulerFactorInverse _ ψ _
    (norm_artinSymbol_le_one
      (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) L q.2) hz

/-! ### Artin `L`-functions -/

/-- **The orders of an Artin `L`-function through a Brauer decomposition into Hecke
`L`-series.** Let `L(s, ρ, L/K) = Π_q Λ_q(s)^{n_q}` on `Re s > 1`, with `Λ_q` the Hecke side of
the ray class character `ψ_q`, and `A = B · L(·, ρ, L/K)` on `Re s > 1` with `A`, `B` analytic
on `Re s > 0`, `B ≢ 0`. For `Re z > 0`: `ord_z A − ord_z B` is the net multiplicity of
`Σ_q n_q Z_{ψ_q}` at `z ≠ 1`, and `−Σ_{q : ψ_q = 1} n_q` at `z = 1`. -/
theorem analyticOrderNatAt_sub_artin_of_brauerHecke (ρ : Representation ℂ G V)
    (n : brauerElementaryMonomialIndex G →₀ ℤ) (c : brauerElementaryMonomialIndex G → ℕ)
    [hc : ∀ q, NeZero (c q)]
    (ψ : ∀ q : brauerElementaryMonomialIndex G, HeckeCharacter (normModulus
      (FixedPoints.intermediateField q.1.subgroup : IntermediateField K L) (c q)))
    (hE : ∀ s : ℂ, 1 < s.re →
      numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s =
        n.prod fun q k => brauerHeckeEulerProduct K L q (c q) (ψ q) s ^ k)
    {A B : ℂ → ℂ} (hA : DifferentiableOn ℂ A {s : ℂ | 0 < s.re})
    (hB : DifferentiableOn ℂ B {s : ℂ | 0 < s.re}) (hB0 : ∃ u : ℂ, 0 < u.re ∧ B u ≠ 0)
    (hAB : ∀ s : ℂ, 1 < s.re → A s = B s *
      numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s) {z : ℂ}
    (hz : 0 < z.re) :
    (analyticOrderNatAt A z : ℤ) - analyticOrderNatAt B z =
      if z = 1 then -(n.sum fun q k => k * (if ψ q = 1 then 1 else 0))
      else netMult n (fun q => rayClassZeros _ (ψ q)) z := by
  refine analyticOrderNatAt_sub_of_configurations n (fun q => rayClassZeros _ (ψ q))
    (fun q => if ψ q = 1 then 1 else 0)
    (fun q => brauerHeckeEulerProduct K L q (c q) (ψ q))
    (fun q => brauerHeckeCleared K L q (c q) (ψ q))
    (fun q => differentiableOn_brauerHeckeCleared K L q (c q) (ψ q))
    (fun q s hs => brauerHeckeCleared_eq K L q (c q) (ψ q) hs)
    (fun q s hs => brauerHeckeEulerProduct_ne_zero K L q (c q) (ψ q) hs)
    (fun q w hw => ?_) (fun q => one_notMem_rayClassZeros _ (ψ q)) hA hB hB0
    (fun s hs => by rw [hAB s hs, hE s hs]) hz
  rw [analyticOrderNatAt_brauerHeckeCleared K L q (c q) (ψ q) hw]
  by_cases h1 : w = 1 <;> by_cases h2 : ψ q = 1 <;> simp [h1, h2]

/-- **The orders of an Artin `L`-function are the net multiplicities of its virtual
configuration.** There are integers `n_q`, tempered configurations `Z_q` and an integer `p`
such that, whenever `A = B · L(·, ρ, L/K)` on `Re s > 1` with `A`, `B` analytic on `Re s > 0`
and `B ≢ 0`:

* `ord_w A − ord_w B = Σ_q n_q m_{Z_q}(w)` at every `w ≠ 1` with `Re w > 0`;
* `ord_1 A − ord_1 B = −p`;
* the form `Σ_q n_q W_{Z_q}` has `m` negative squares on some family of `m` tests iff at least
  `m` points are zeros or poles of `A / B` right of the critical line, other than `1`, or poles
  of `A / B` on the line. -/
theorem exists_virtualConfig_artin (ρ : Representation ℂ G V) :
    ∃ (n : brauerElementaryMonomialIndex G →₀ ℤ)
      (Z : brauerElementaryMonomialIndex G → ZeroConfig) (p : ℤ),
      (∀ q, SquareRootThreshold.TemperedConfig (Z q)) ∧
      ∀ A B : ℂ → ℂ, DifferentiableOn ℂ A {s : ℂ | 0 < s.re} →
        DifferentiableOn ℂ B {s : ℂ | 0 < s.re} → (∃ u : ℂ, 0 < u.re ∧ B u ≠ 0) →
        (∀ s : ℂ, 1 < s.re → A s = B s *
          numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s) →
        (∀ w : ℂ, 0 < w.re → w ≠ 1 →
          (analyticOrderNatAt A w : ℤ) - analyticOrderNatAt B w = netMult n Z w) ∧
        (analyticOrderNatAt A 1 : ℤ) - analyticOrderNatAt B 1 = -p ∧
        ∀ m : ℕ, (∃ f : Fin m → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧
            (∀ i, HasCompactSupport (f i)) ∧
            m ≤ hermNegIndex (n.sum fun q k => (k : ℂ) • zeroGram (Z q) f)) ↔
          (m : ℕ∞) ≤ ({w : ℂ | 1 / 2 < w.re ∧ w ≠ 1 ∧
              analyticOrderNatAt A w ≠ analyticOrderNatAt B w} ∪
            {w : ℂ | w.re = 1 / 2 ∧
              analyticOrderNatAt A w < analyticOrderNatAt B w}).encard := by
  obtain ⟨n, Λ, hΛ, hE⟩ := exists_artinEulerProduct_eq_prod_zpow_heckeL K L ρ
  unfold IsBrauerHeckeEulerProduct at hΛ
  choose c hc ψ hψ using hΛ
  have hE' : ∀ s : ℂ, 1 < s.re →
      numberFieldFinitePlaceArtinEulerReciprocalProduct (K := K) (L := L) ρ s =
        n.prod fun q k => brauerHeckeEulerProduct K L q (c q) (ψ q) s ^ k := fun s hs => by
    rw [hE s hs]
    exact Finsupp.prod_congr fun q _ => by rw [hψ q s]
  refine ⟨n, fun q => rayClassZeros _ (ψ q),
    n.sum fun q k => k * (if ψ q = 1 then 1 else 0),
    fun q => temperedConfig_rayClassZeros _ (ψ q), fun A B hA hB hB0 hAB => ?_⟩
  have hord := fun (w : ℂ) (hw : 0 < w.re) =>
    analyticOrderNatAt_sub_artin_of_brauerHecke K L ρ n c ψ hE' hA hB hB0 hAB hw
  have hne : ∀ w : ℂ, 0 < w.re → w ≠ 1 →
      (analyticOrderNatAt A w : ℤ) - analyticOrderNatAt B w =
        netMult n (fun q => rayClassZeros _ (ψ q)) w := fun w hw h1 => by
    rw [hord w hw, if_neg h1]
  refine ⟨hne, by rw [hord 1 (by simp), if_pos rfl], fun m => ?_⟩
  have hidx := exists_le_negIndex_combination_iff n (fun q => rayClassZeros _ (ψ q))
    (fun q => temperedConfig_rayClassZeros _ (ψ q)) m
  rw [combinationDefect_eq_of_orders n (fun q => rayClassZeros _ (ψ q))
    (fun q => one_notMem_rayClassZeros _ (ψ q)) hne] at hidx
  exact hidx

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
