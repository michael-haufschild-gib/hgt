import Mathlib

/-!
# Purity without positivity is multiplicity one

The Riemann hypothesis for a curve says that every eigenvalue `α` of the Frobenius on `H¹`
satisfies `α ᾱ = q`. Two structures are available without any positivity: the duality pairing,
for which the Frobenius is a similitude of factor `q` (the functional equation), and complex
conjugation of the coefficients, which commutes with the Frobenius (the archimedean place of the
coefficient field). On an eigenvector `v` they give `α ᾱ ⟨v, v̄⟩ = q ⟨v, v̄⟩`
(`mul_conj_eq_of_pair_bar_ne_zero`): purity holds as soon as `v` is not orthogonal to its
conjugate.

A finite symmetry group commuting with the three structures decides when this happens. The
pairing couples the `χ`-eigenspace only with the `χ⁻¹`-eigenspace
(`pair_eq_zero_of_isEigen`), and conjugation exchanges the two.

* `exists_eigenvalue_mul_conj_eq`: if the `χ`-eigenspace is a line, the Frobenius acts on it by
  a scalar `α` with `α ᾱ = q`. This is the mechanism of the Jacobi sums: each character of
  `μ_m × μ_m` occurs once in `H¹` of a Kummer curve, conjugation and duality both send the
  line of `χ` to the line of `χ⁻¹`, and so they agree on the eigenvalue.
* `exists_frobenius_not_pure`: on a two-dimensional eigenspace the same axioms hold for the
  Frobenius `diag(r, r⁻¹)`, for every real `r ≠ 0`.
* `exists_frobenius_not_pure_of_scaling`: with the non-compact group `ℝˣ` acting by
  `diag(t, t⁻¹)` every eigenspace is a line and the same Frobenius is not pure. The character
  `t ↦ t` is not unitary: conjugation fixes its line, while the pairing couples it with the
  other line.

Both hypotheses of the purity theorem, a compact symmetry and multiplicity one, are needed.

For the zeros of `ζ` the two structures are `ρ ↦ ρ̄` and `ρ ↦ 1 − ρ`; they agree on a zero iff
it lies on the critical line. The compact symmetry, the Dirichlet characters, has infinite
multiplicity; the scaling group acts on the line of a zero `ρ` by `t ↦ t^(ρ − 1/2)`, which is
unitary iff `Re ρ = 1/2`.
-/

open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticProducerTheory

/-- A Frobenius on a complex vector space with the three positivity-free structures of the
cohomology of a curve: a pairing scaled by `q`, a conjugation commuting with the Frobenius, and a
symmetry group commuting with all of them. -/
structure SymmetricFrobenius (G V : Type*) [Group G] [AddCommGroup V] [Module ℂ V] where
  /-- the Frobenius -/
  frob : Module.End ℂ V
  /-- the duality pairing -/
  pair : V →ₗ[ℂ] V →ₗ[ℂ] ℂ
  /-- complex conjugation of the coefficients -/
  bar : V → V
  /-- the symmetry group -/
  act : G →* Module.End ℂ V
  /-- the weight -/
  q : ℂ
  pair_frob : ∀ x y, pair (frob x) (frob y) = q * pair x y
  bar_add : ∀ x y, bar (x + y) = bar x + bar y
  bar_smul : ∀ (z : ℂ) (x : V), bar (z • x) = conj z • bar x
  bar_bar : ∀ x, bar (bar x) = x
  bar_frob : ∀ x, bar (frob x) = frob (bar x)
  act_frob : ∀ g x, act g (frob x) = frob (act g x)
  act_bar : ∀ g x, act g (bar x) = bar (act g x)
  pair_act : ∀ g x y, pair (act g x) (act g y) = pair x y

namespace SymmetricFrobenius

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] {D : SymmetricFrobenius G V}

/-- **The two pairings on one line.** An eigenvector not orthogonal to its conjugate has a pure
eigenvalue: the pairing gives `α α' = q` for the eigenvalue `α'` of `v̄`, and conjugation
gives `α' = ᾱ`. -/
theorem mul_conj_eq_of_pair_bar_ne_zero {v : V} {α : ℂ} (hv : D.frob v = α • v)
    (hne : D.pair v (D.bar v) ≠ 0) : α * conj α = D.q := by
  have h := D.pair_frob v (D.bar v)
  rw [← D.bar_frob, hv, D.bar_smul] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  exact mul_right_cancel₀ hne (by linear_combination h)

/-- `v` lies in the `χ`-eigenspace of the symmetry group. -/
def IsEigen (D : SymmetricFrobenius G V) (χ : G →* ℂ) (v : V) : Prop := ∀ g, D.act g v = χ g • v

/-- The Frobenius preserves every eigenspace of the symmetry group. -/
theorem IsEigen.frob {χ : G →* ℂ} {v : V} (h : D.IsEigen χ v) : D.IsEigen χ (D.frob v) :=
  fun g => by rw [D.act_frob, h g, map_smul]

/-- Conjugation sends the `χ`-eigenspace to the `χ̄`-eigenspace. -/
theorem IsEigen.act_bar {χ : G →* ℂ} {v : V} (h : D.IsEigen χ v) (g : G) :
    D.act g (D.bar v) = conj (χ g) • D.bar v := by
  rw [D.act_bar, h g, D.bar_smul]

/-- The pairing couples the `χ`-eigenspace only with the `χ⁻¹`-eigenspace. -/
theorem pair_eq_zero_of_isEigen {χ ψ : G →* ℂ} {x y : V} (hx : D.IsEigen χ x)
    (hy : D.IsEigen ψ y) {g : G} (hg : χ g * ψ g ≠ 1) : D.pair x y = 0 := by
  have h := D.pair_act g x y
  rw [hx g, hy g] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  by_contra hne
  exact hg (mul_right_cancel₀ hne (by linear_combination h))

/-- A character of a finite group has unimodular values. -/
theorem conj_eq_inv_of_finite [Finite G] (χ : G →* ℂ) (g : G) : conj (χ g) = (χ g)⁻¹ := by
  have hpow : χ g ^ Nat.card G = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  have hnorm : ‖χ g‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow Nat.card_pos.ne'
  exact (Complex.inv_eq_conj hnorm).symm

variable [Fintype G]

/-- The projector to the `χ⁻¹`-eigenspace. -/
def proj (D : SymmetricFrobenius G V) (χ : G →* ℂ) (w : V) : V :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, χ g • D.act g w

theorem act_proj (χ : G →* ℂ) (w : V) (h : G) :
    D.act h (D.proj χ w) = (χ h)⁻¹ • D.proj χ w := by
  have hχ : χ h ≠ 0 := fun h0 => by
    have h1 := map_mul χ h h⁻¹
    rw [mul_inv_cancel, map_one, h0, zero_mul] at h1
    exact one_ne_zero h1
  have key : ∑ g : G, χ g • D.act h (D.act g w) = (χ h)⁻¹ • ∑ g : G, χ g • D.act g w := by
    rw [← Equiv.sum_comp (Equiv.mulLeft h) fun g => χ g • D.act g w, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    show χ g • D.act h (D.act g w) = (χ h)⁻¹ • (χ (h * g) • D.act (h * g) w)
    rw [map_mul χ, map_mul D.act, Module.End.mul_apply, smul_smul, ← mul_assoc,
      inv_mul_cancel₀ hχ, one_mul]
  rw [proj, map_smul, map_sum]
  simp only [map_smul]
  rw [key, smul_comm]

/-- Against a `χ`-eigenvector the pairing only sees the `χ⁻¹`-component. -/
theorem pair_proj {χ : G →* ℂ} {v : V} (hv : D.IsEigen χ v) (w : V) :
    D.pair v (D.proj χ w) = D.pair v w := by
  have hterm : ∀ g : G, χ g * D.pair v (D.act g w) = D.pair v w := fun g => by
    have h := D.pair_act g⁻¹ v (D.act g w)
    rw [hv g⁻¹, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    have h1 : χ g * χ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [← h]
    linear_combination D.pair v w * h1
  rw [proj, map_smul, map_sum]
  simp only [map_smul, smul_eq_mul, hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

/-- **Purity at multiplicity one.** If the `χ`-eigenspace of the symmetry group is the line of
`v` and `v` is not in the kernel of the pairing, the Frobenius acts on the line by a scalar `α`
with `α ᾱ = q`. No positivity enters: the `χ⁻¹`-eigenspace is the conjugate line, so the
vector dual to `v` is a multiple of `v̄`. -/
theorem exists_eigenvalue_mul_conj_eq {χ : G →* ℂ} {v : V} (hv : D.IsEigen χ v)
    (hline : ∀ w, D.IsEigen χ w → ∃ c : ℂ, w = c • v) (hnd : ∃ w, D.pair v w ≠ 0) :
    ∃ α : ℂ, D.frob v = α • v ∧ α * conj α = D.q := by
  obtain ⟨α, hα⟩ := hline _ hv.frob
  refine ⟨α, hα, mul_conj_eq_of_pair_bar_ne_zero hα ?_⟩
  obtain ⟨w, hw⟩ := hnd
  -- the conjugate of the `χ⁻¹`-component of `w` lies on the line of `v`
  have hbar : D.IsEigen χ (D.bar (D.proj χ w)) := fun g => by
    rw [D.act_bar, act_proj, D.bar_smul, map_inv₀, conj_eq_inv_of_finite χ g, inv_inv]
  obtain ⟨c, hc⟩ := hline _ hbar
  have hw' : D.proj χ w = conj c • D.bar v := by
    rw [← D.bar_smul, ← hc, D.bar_bar]
  have h2 := pair_proj hv w
  rw [hw', map_smul, smul_eq_mul] at h2
  intro h0
  rw [h0, mul_zero] at h2
  exact hw h2.symm

end SymmetricFrobenius

/-! ### The twin at multiplicity two -/

/-- The split datum on `ℂ²`: Frobenius `diag(r, r⁻¹)`, hyperbolic pairing, coordinatewise
conjugation, trivial symmetry, weight `1`. -/
def splitTwin (r : ℝ) (hr : r ≠ 0) : SymmetricFrobenius Unit (ℂ × ℂ) where
  frob := LinearMap.prodMap ((r : ℂ) • LinearMap.id) ((r : ℂ)⁻¹ • LinearMap.id)
  pair := LinearMap.mk₂ ℂ (fun a b => a.1 * b.2 + a.2 * b.1)
    (fun a a' b => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c a b => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun a b b' => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun c a b => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
  bar := fun a => (conj a.1, conj a.2)
  act := 1
  q := 1
  pair_frob := fun x y => by
    have hr' : (r : ℂ) * (r : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr)
    simp only [LinearMap.mk₂_apply, LinearMap.prodMap_apply, LinearMap.smul_apply,
      LinearMap.id_apply, smul_eq_mul, one_mul]
    linear_combination (x.1 * y.2 + x.2 * y.1) * hr'
  bar_add := fun x y => by simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]
  bar_smul := fun z x => by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul, Prod.smul_mk]
  bar_bar := fun x => by simp only [Complex.conj_conj, Prod.mk.eta]
  bar_frob := fun x => by
    simp only [LinearMap.prodMap_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
      map_mul, map_inv₀, Complex.conj_ofReal]
  act_frob := fun _ _ => by simp only [MonoidHom.one_apply, Module.End.one_apply]
  act_bar := fun _ _ => by simp only [MonoidHom.one_apply, Module.End.one_apply]
  pair_act := fun _ _ _ => by simp only [MonoidHom.one_apply, Module.End.one_apply]

theorem splitTwin_frob (r : ℝ) (hr : r ≠ 0) :
    (splitTwin r hr).frob (1, 0) = (r : ℂ) • ((1, 0) : ℂ × ℂ) := by
  simp only [splitTwin, LinearMap.prodMap_apply, LinearMap.smul_apply, LinearMap.id_apply,
    smul_eq_mul, mul_one, mul_zero, Prod.smul_mk]

/-- The pairing of the split datum is nondegenerate. -/
theorem splitTwin_nondegenerate (r : ℝ) (hr : r ≠ 0) {a : ℂ × ℂ} (ha : a ≠ 0) :
    ∃ b, (splitTwin r hr).pair a b ≠ 0 := by
  by_cases h1 : a.1 = 0
  · have h2 : a.2 ≠ 0 := fun h2 => ha (Prod.ext h1 h2)
    refine ⟨(1, 0), ?_⟩
    simpa only [splitTwin, LinearMap.mk₂_apply, mul_zero, mul_one, zero_add] using h2
  · refine ⟨(0, 1), ?_⟩
    simpa only [splitTwin, LinearMap.mk₂_apply, mul_zero, mul_one, add_zero] using h1

private theorem ofReal_mul_conj_ne_one {r : ℝ} (hr1 : r ^ 2 ≠ 1) :
    (r : ℂ) * conj (r : ℂ) ≠ 1 := by
  intro h'
  apply hr1
  rw [Complex.conj_ofReal] at h'
  have h'' : ((r ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    push_cast
    rw [← h']
    ring
  exact Complex.ofReal_injective h''

/-- **The axioms do not force purity at multiplicity two.** A Frobenius with a functional
equation and a real structure on a nondegenerate two-dimensional space can have an eigenvalue of
any real modulus. -/
theorem exists_frobenius_not_pure (r : ℝ) (hr : r ≠ 0) (hr1 : r ^ 2 ≠ 1) :
    ∃ D : SymmetricFrobenius Unit (ℂ × ℂ), D.q = 1 ∧ (∀ a, a ≠ 0 → ∃ b, D.pair a b ≠ 0) ∧
      ∃ (v : ℂ × ℂ) (α : ℂ), v ≠ 0 ∧ D.frob v = α • v ∧ α * conj α ≠ D.q := by
  refine ⟨splitTwin r hr, rfl, fun a ha => splitTwin_nondegenerate r hr ha, (1, 0), (r : ℂ),
    ?_, splitTwin_frob r hr, ?_⟩
  · intro h
    exact one_ne_zero (congrArg Prod.fst h)
  · exact ofReal_mul_conj_ne_one hr1

/-! ### The twin with a non-compact symmetry -/

/-- `diag(t, t⁻¹)` on `ℂ²`. -/
def scalingMap (t : ℂ) : Module.End ℂ (ℂ × ℂ) :=
  LinearMap.prodMap (t • LinearMap.id) (t⁻¹ • LinearMap.id)

theorem scalingMap_apply (t : ℂ) (a : ℂ × ℂ) : scalingMap t a = (t * a.1, t⁻¹ * a.2) := rfl

/-- The scaling action `t ↦ diag(t, t⁻¹)` of `ℝˣ` on `ℂ²`. -/
def scalingAct : ℝˣ →* Module.End ℂ (ℂ × ℂ) where
  toFun t := scalingMap ((t : ℝ) : ℂ)
  map_one' := LinearMap.ext fun a => by
    simp only [scalingMap_apply, Units.val_one, Complex.ofReal_one, inv_one, one_mul,
      Module.End.one_apply, Prod.mk.eta]
  map_mul' s t := LinearMap.ext fun a => by
    simp only [Module.End.mul_apply, scalingMap_apply, Units.val_mul, Complex.ofReal_mul,
      Prod.mk.injEq]
    exact ⟨by ring, by ring⟩

theorem scalingAct_apply (t : ℝˣ) (a : ℂ × ℂ) :
    scalingAct t a = (((t : ℝ) : ℂ) * a.1, ((t : ℝ) : ℂ)⁻¹ * a.2) := rfl

/-- The character `t ↦ t` of `ℝˣ`; it is not unitary. -/
def scalingChar : ℝˣ →* ℂ where
  toFun t := ((t : ℝ) : ℂ)
  map_one' := by simp only [Units.val_one, Complex.ofReal_one]
  map_mul' s t := by simp only [Units.val_mul, Complex.ofReal_mul]

theorem scalingChar_apply (t : ℝˣ) : scalingChar t = ((t : ℝ) : ℂ) := rfl

/-- The split datum with the symmetry `ℝˣ` acting by `diag(t, t⁻¹)`. -/
def scalingTwin (r : ℝ) (hr : r ≠ 0) : SymmetricFrobenius ℝˣ (ℂ × ℂ) where
  frob := (splitTwin r hr).frob
  pair := (splitTwin r hr).pair
  bar := (splitTwin r hr).bar
  act := scalingAct
  q := (splitTwin r hr).q
  pair_frob := (splitTwin r hr).pair_frob
  bar_add := (splitTwin r hr).bar_add
  bar_smul := (splitTwin r hr).bar_smul
  bar_bar := (splitTwin r hr).bar_bar
  bar_frob := (splitTwin r hr).bar_frob
  act_frob := fun t x => by
    simp only [scalingAct_apply, splitTwin, LinearMap.prodMap_apply, LinearMap.smul_apply,
      LinearMap.id_apply, smul_eq_mul, Prod.mk.injEq]
    exact ⟨by ring, by ring⟩
  act_bar := fun t x => by
    simp only [scalingAct_apply, splitTwin, map_mul, map_inv₀, Complex.conj_ofReal]
  pair_act := fun t x y => by
    have ht : ((t : ℝ) : ℂ) * ((t : ℝ) : ℂ)⁻¹ = 1 :=
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr t.ne_zero)
    simp only [scalingAct_apply, splitTwin, LinearMap.mk₂_apply]
    linear_combination (x.1 * y.2 + x.2 * y.1) * ht

/-- **The axioms do not force purity under a non-compact symmetry.** With `ℝˣ` acting by
`diag(t, t⁻¹)` the eigenspace of the character `t ↦ t` is the line of `(1, 0)`, the pairing does
not vanish on it, and the Frobenius `diag(r, r⁻¹)` commutes with the pairing, the conjugation and
the symmetry; its eigenvalue `r` is not pure. -/
theorem exists_frobenius_not_pure_of_scaling (r : ℝ) (hr : r ≠ 0) (hr1 : r ^ 2 ≠ 1) :
    ∃ (D : SymmetricFrobenius ℝˣ (ℂ × ℂ)) (χ : ℝˣ →* ℂ) (v : ℂ × ℂ),
      D.q = 1 ∧ D.IsEigen χ v ∧ (∀ w, D.IsEigen χ w → ∃ c : ℂ, w = c • v) ∧
        (∃ w, D.pair v w ≠ 0) ∧ ∃ α : ℂ, D.frob v = α • v ∧ α * conj α ≠ D.q := by
  refine ⟨scalingTwin r hr, scalingChar, (1, 0), rfl, ?_, ?_, ?_, (r : ℂ), splitTwin_frob r hr,
    ofReal_mul_conj_ne_one hr1⟩
  · intro t
    show scalingAct t (1, 0) = scalingChar t • ((1, 0) : ℂ × ℂ)
    rw [scalingAct_apply, scalingChar_apply]
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero]
  · intro w hw
    -- the element `2` of the group separates the two lines
    have h2 : scalingAct (Units.mk0 (2 : ℝ) two_ne_zero) w =
        scalingChar (Units.mk0 (2 : ℝ) two_ne_zero) • w := hw _
    rw [scalingAct_apply, scalingChar_apply] at h2
    have h3 := congrArg Prod.snd h2
    simp only [Units.val_mk0, Complex.ofReal_ofNat, Prod.smul_snd, smul_eq_mul] at h3
    have hw2 : w.2 = 0 := by linear_combination (-2 / 3 : ℂ) * h3
    exact ⟨w.1, Prod.ext (by simp) (by simp [hw2])⟩
  · exact splitTwin_nondegenerate r hr fun h => one_ne_zero (congrArg Prod.fst h)

end GaloisForLFunctions.ArithmeticProducerTheory
