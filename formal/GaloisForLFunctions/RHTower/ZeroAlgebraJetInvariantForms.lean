import GaloisForLFunctions.RHTower.XiSuperchargeHarnackDefect
import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# Invariant Hermitian forms on the zero algebra of `Ξ`

The zero algebra `A = O/(Ξ)` on finitely supported data is the direct sum of the jet spaces
`ℂ[ε]/(ε^{m_ρ})` at the zeros `ρ` of `Ξ` (multiplicity `m_ρ`).  Multiplication by `q^{iz}`,
`q ∈ ℚ_{>0}`, acts on the jet at `ρ` by the character `q^{iρ}` times the unipotent operator
`exp(i ε log q)`; on basis jets, `ε^k ↦ Σ_{l ≥ k} e^{iaρ} (ia)^{l-k}/(l-k)! ε^l`, `a = log q`.

* `invariantForm_eq_zero_of_ne_conj` (support law): an invariant Hermitian form pairs the jets at
  `ρ` and `σ` only when `σ = conj ρ`; the proof needs `q^{iw} ≠ 1` for some rational `q` when
  `w ≠ 0` (`exists_rat_exp_ne_one`, from `2^a ≠ 3^b`).
* `invariantForm_higherJet_radical`: at a real point, a positive semidefinite invariant form
  vanishes on every jet of order `≥ 1`, so it sees only the value `F(ρ)`.
* `posDef_invariantForm_real_simple`: a positive-definite invariant form forces every point to be
  real and every multiplicity to be one.
* `valuePairing`, `valueForm`: `Σ_ρ conj F(ρ) G(ρ)` is a positive semidefinite invariant form
  whenever every point is real, and positive definite when every multiplicity is one
  (`exists_posDef_invariantForm`).
* `exists_posDef_invariantForm_XiC_iff`: a positive-definite invariant form on the zero algebra of
  `Ξ` exists iff RH holds and every zero of `Ξ` is simple.
-/

open Complex
open scoped Real ComplexConjugate

namespace RHTower.ZeroAlgebraInvariantForms

noncomputable section

variable {ι : Type*}

/-! ### The jet model -/

/-- Basis labels `(ρ, k)`, `k < m_ρ`, of the jet spaces. -/
abbrev JetIndex (m : ι → ℕ) := Σ i, Fin (m i)

/-- The zero algebra on finitely supported jet data. -/
abbrev ZeroAlgebra (m : ι → ℕ) := JetIndex m →₀ ℂ

/-- The coefficient of `ε^n` in the jet of `e^{iaz}` at `ρ`. -/
def jetCoeff (ρ : ℂ) (a : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (I*a*ρ)*(I*a)^n/(n.factorial : ℂ)

/-- The basis jet `ε^k` at the point `i`. -/
def e {m : ι → ℕ} (i : ι) (k : Fin (m i)) : ZeroAlgebra m := Finsupp.single ⟨i, k⟩ 1

/-- Multiplication by `e^{iaz}` on the basis jet `ε^k` at the point `i`. -/
def actBasis (ρ : ι → ℂ) (m : ι → ℕ) (a : ℝ) (p : JetIndex m) : ZeroAlgebra m :=
  ∑ l : Fin (m p.1), if p.2≤l then jetCoeff (ρ p.1) a ((l:ℕ)-(p.2:ℕ)) • e p.1 l else 0

/-- The action of `M_q`, `a = log q`, on the zero algebra. -/
def act (ρ : ι → ℂ) (m : ι → ℕ) (a : ℝ) : ZeroAlgebra m →ₗ[ℂ] ZeroAlgebra m :=
  Finsupp.linearCombination ℂ (actBasis ρ m a)

/-- An `M`-invariant Hermitian form on the zero algebra. -/
structure InvariantForm (ρ : ι → ℂ) (m : ι → ℕ) where
  /-- The sesquilinear form. -/
  form : ZeroAlgebra m →ₗ⋆[ℂ] ZeroAlgebra m →ₗ[ℂ] ℂ
  /-- Hermitian symmetry. -/
  hermitian : ∀ x y, conj (form x y)=form y x
  /-- Invariance under every `M_q`, `q ∈ ℚ_{>0}`. -/
  invariant : ∀ q : ℚ, 0<q → ∀ x y,
    form (act ρ m (Real.log q) x) (act ρ m (Real.log q) y)=form x y

variable {ρ : ι → ℂ} {m : ι → ℕ}

theorem act_e (a : ℝ) (i : ι) (k : Fin (m i)) :
    act ρ m a (e i k)=∑ l : Fin (m i), if k≤l then jetCoeff (ρ i) a ((l:ℕ)-(k:ℕ)) • e i l
      else 0 := by
  rw [act, e, Finsupp.linearCombination_single, one_smul]
  rfl

theorem jetCoeff_zero (z : ℂ) (a : ℝ) : jetCoeff z a 0=Complex.exp (I*a*z) := by
  simp [jetCoeff]

theorem jetCoeff_one (z : ℂ) (a : ℝ) : jetCoeff z a 1=Complex.exp (I*a*z)*(I*a) := by
  simp [jetCoeff]

/-- On the top jet the action is the character `e^{iaρ}`. -/
theorem act_e_top (a : ℝ) (i : ι) (k : Fin (m i)) (hk : (k:ℕ)+1=m i) :
    act ρ m a (e i k)=Complex.exp (I*a*ρ i) • e i k := by
  rw [act_e, Finset.sum_eq_single k]
  · rw [if_pos le_rfl, Nat.sub_self, jetCoeff_zero]
  · intro l _ hlk
    rw [if_neg]
    intro hkl
    have hl : (l:ℕ)≤k := by have := l.isLt; omega
    exact hlk (Fin.ext (le_antisymm hl hkl))
  · intro h; exact absurd (Finset.mem_univ k) h

/-! ### Sesquilinear bookkeeping -/

theorem form_smul_left (H : InvariantForm ρ m) (c : ℂ) (u v : ZeroAlgebra m) :
    H.form (c • u) v=conj c*H.form u v := by
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]

theorem form_smul_right (H : InvariantForm ρ m) (c : ℂ) (u v : ZeroAlgebra m) :
    H.form u (c • v)=c*H.form u v := by
  rw [map_smul, smul_eq_mul]

theorem form_add_left (H : InvariantForm ρ m) (u u' v : ZeroAlgebra m) :
    H.form (u+u') v=H.form u v+H.form u' v := by
  rw [map_add, LinearMap.add_apply]

theorem form_add_right (H : InvariantForm ρ m) (u v v' : ZeroAlgebra m) :
    H.form u (v+v')=H.form u v+H.form u v' :=
  map_add _ _ _

theorem form_sum_left {α : Type*} (H : InvariantForm ρ m) (s : Finset α) (f : α → ZeroAlgebra m)
    (v : ZeroAlgebra m) : H.form (∑ x ∈ s, f x) v=∑ x ∈ s, H.form (f x) v := by
  rw [map_sum, LinearMap.sum_apply]

theorem form_sum_right {α : Type*} (H : InvariantForm ρ m) (s : Finset α) (f : α → ZeroAlgebra m)
    (u : ZeroAlgebra m) : H.form u (∑ x ∈ s, f x)=∑ x ∈ s, H.form u (f x) :=
  map_sum _ _ _

theorem form_zero_left (H : InvariantForm ρ m) (v : ZeroAlgebra m) : H.form 0 v=0 := by
  rw [map_zero, LinearMap.zero_apply]

theorem form_zero_right (H : InvariantForm ρ m) (u : ZeroAlgebra m) : H.form u 0=0 :=
  map_zero _

/-- Pairing of two actions on basis jets as a double sum. -/
theorem form_act_e (H : InvariantForm ρ m) (a : ℝ) (i j : ι) (k : Fin (m i)) (l : Fin (m j)) :
    H.form (act ρ m a (e i k)) (act ρ m a (e j l))=
      ∑ k' : Fin (m i), ∑ l' : Fin (m j),
        if k≤k' ∧ l≤l' then conj (jetCoeff (ρ i) a ((k':ℕ)-(k:ℕ)))*
          jetCoeff (ρ j) a ((l':ℕ)-(l:ℕ))*H.form (e i k') (e j l') else 0 := by
  rw [act_e, act_e, form_sum_left]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [form_sum_right]
  refine Finset.sum_congr rfl fun l' _ => ?_
  by_cases hk : k≤k' <;> by_cases hl : l≤l'
  · rw [if_pos hk, if_pos hl, if_pos ⟨hk, hl⟩, form_smul_left, form_smul_right]; ring
  · rw [if_neg hl, form_zero_right, if_neg (fun h => hl h.2)]
  · rw [if_neg hk, form_zero_left, if_neg (fun h => hk h.1)]
  · rw [if_neg hk, form_zero_left, if_neg (fun h => hk h.1)]

/-! ### Characters at rational points -/

/-- A nonzero frequency is detected by some rational `q`: `q^{iw} ≠ 1`.  Otherwise `w log 2` and
`w log 3` would both lie in `2πℤ`, forcing `2^b = 3^a` with `a ≠ 0`. -/
theorem exists_rat_exp_ne_one {w : ℂ} (hw : w≠0) :
    ∃ q : ℚ, 0<q ∧ Complex.exp (I*(Real.log q : ℂ)*w)≠1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hcon 2 (by norm_num))
  obtain ⟨n', hn'⟩ := Complex.exp_eq_one_iff.mp (hcon 3 (by norm_num))
  have hl2 : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : (0:ℝ)<Real.log 3 := Real.log_pos (by norm_num)
  have hπ := Real.pi_pos
  have hIne : (I : ℂ)≠0 := Complex.I_ne_zero
  push_cast at hn hn'
  have hw2 : (Real.log 2 : ℂ)*w=2*π*n := by
    apply mul_left_cancel₀ hIne
    linear_combination hn
  have hw3 : (Real.log 3 : ℂ)*w=2*π*n' := by
    apply mul_left_cancel₀ hIne
    linear_combination hn'
  have hπC : (π : ℂ)≠0 := by exact_mod_cast hπ.ne'
  have hcrossC : ((n':ℂ)*Real.log 2)=((n:ℂ)*Real.log 3) := by
    apply mul_left_cancel₀ (show (2*π : ℂ)≠0 by simp [hπC])
    linear_combination (Real.log 3 : ℂ)*hw2-(Real.log 2 : ℂ)*hw3
  have hcrossR : (n':ℝ)*Real.log 2=(n:ℝ)*Real.log 3 := by exact_mod_cast hcrossC
  have hn0 : n≠0 := by
    intro h0
    rw [h0] at hw2
    simp only [Int.cast_zero, mul_zero, mul_eq_zero] at hw2
    exact hw (hw2.resolve_left (by exact_mod_cast hl2.ne'))
  have key : ∀ a b : ℕ, 0<b → (a:ℝ)*Real.log 2=(b:ℝ)*Real.log 3 → False := by
    intro a b hb hab
    have h := congrArg Real.exp hab
    rw [← Real.log_pow, ← Real.log_pow, Real.exp_log (by positivity),
      Real.exp_log (by positivity)] at h
    have hnat : 2^a=3^b := by exact_mod_cast h
    have h3 : ¬ 2∣3^b := by
      intro hd
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hd
      omega
    rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, pow_zero] at hnat
      have : 1<3^b := Nat.one_lt_pow hb.ne' (by norm_num)
      omega
    · exact h3 (hnat ▸ dvd_pow_self 2 ha.ne')
  rcases lt_or_gt_of_ne hn0 with hneg | hpos
  · have hnR : (n:ℝ)<0 := by exact_mod_cast hneg
    have hn'R : (n':ℝ)<0 := by
      by_contra hc
      push Not at hc
      nlinarith
    have hn' : n'<0 := by exact_mod_cast hn'R
    apply key (-n').toNat (-n).toNat (by omega)
    rw [show (((-n').toNat : ℕ) : ℝ)=-(n':ℝ) by
        rw [show (((-n').toNat : ℕ) : ℝ)=(((-n').toNat : ℤ) : ℝ) by norm_cast,
          Int.toNat_of_nonneg (by omega)]; push_cast; ring,
      show (((-n).toNat : ℕ) : ℝ)=-(n:ℝ) by
        rw [show (((-n).toNat : ℕ) : ℝ)=(((-n).toNat : ℤ) : ℝ) by norm_cast,
          Int.toNat_of_nonneg (by omega)]; push_cast; ring]
    linarith
  · have hnR : (0:ℝ)<n := by exact_mod_cast hpos
    have hn'R : (0:ℝ)≤n' := by
      by_contra hc
      push Not at hc
      nlinarith
    have hn' : 0≤n' := by exact_mod_cast hn'R
    apply key n'.toNat n.toNat (by omega)
    rw [show ((n'.toNat : ℕ) : ℝ)=((n'.toNat : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg hn',
      show ((n.toNat : ℕ) : ℝ)=((n.toNat : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg hpos.le]
    exact hcrossR

theorem conj_exp_mul_exp (z w : ℂ) (a : ℝ) :
    conj (Complex.exp (I*a*z))*Complex.exp (I*a*w)=Complex.exp (I*(a:ℂ)*(w-conj z)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem conj_exp_mul_exp_self_of_real {z : ℂ} (hz : z.im=0) (a : ℝ) :
    conj (Complex.exp (I*a*z))*Complex.exp (I*a*z)=1 := by
  rw [conj_exp_mul_exp]
  have : z-conj z=0 := by apply Complex.ext <;> simp [hz]
  rw [this, mul_zero, Complex.exp_zero]

/-! ### The support law -/

/-- **Support law.**  An invariant form pairs the jets at `i` and `j` only when `ρ_j = conj ρ_i`. -/
theorem invariantForm_eq_zero_of_ne_conj (H : InvariantForm ρ m) {i j : ι}
    (hij : ρ j≠conj (ρ i)) (k : Fin (m i)) (l : Fin (m j)) :
    H.form (e i k) (e j l)=0 := by
  obtain ⟨q, hq, hne⟩ := exists_rat_exp_ne_one (sub_ne_zero.mpr hij)
  suffices hsuff : ∀ d : ℕ, ∀ k : Fin (m i), ∀ l : Fin (m j),
      (m i-1-(k:ℕ))+(m j-1-(l:ℕ))=d → H.form (e i k) (e j l)=0 from hsuff _ k l rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro k l hd
  have hinv := H.invariant q hq (e i k) (e j l)
  rw [form_act_e] at hinv
  have hrest : ∀ k' : Fin (m i), ∀ l' : Fin (m j), (k', l')≠(k, l) →
      (if k≤k' ∧ l≤l' then conj (jetCoeff (ρ i) (Real.log q) ((k':ℕ)-(k:ℕ)))*
        jetCoeff (ρ j) (Real.log q) ((l':ℕ)-(l:ℕ))*H.form (e i k') (e j l') else 0)=0 := by
    intro k' l' hne'
    split_ifs with hkl
    · have hk'' : (k:ℕ)≤k' := hkl.1
      have hl'' : (l:ℕ)≤l' := hkl.2
      have hor : (k:ℕ)<k' ∨ (l:ℕ)<l' := by
        by_contra hc
        push Not at hc
        exact hne' (Prod.ext (Fin.ext (show (k':ℕ)=k by omega))
          (Fin.ext (show (l':ℕ)=l by omega)))
      have hlt : (m i-1-(k':ℕ))+(m j-1-(l':ℕ))<d := by
        have := k'.isLt
        have := l'.isLt
        omega
      rw [ih _ hlt k' l' rfl, mul_zero]
    · rfl
  rw [Finset.sum_eq_single k (fun k' _ hk' => Finset.sum_eq_zero fun l' _ =>
      hrest k' l' (fun h => hk' (congrArg Prod.fst h))) (fun h => absurd (Finset.mem_univ k) h),
    Finset.sum_eq_single l (fun l' _ hl' => hrest k l' (fun h => hl' (congrArg Prod.snd h)))
      (fun h => absurd (Finset.mem_univ l) h),
    if_pos ⟨le_rfl, le_rfl⟩, Nat.sub_self, Nat.sub_self, jetCoeff_zero, jetCoeff_zero,
    conj_exp_mul_exp] at hinv
  have hfac : (Complex.exp (I*(Real.log q : ℂ)*(ρ j-conj (ρ i)))-1)*H.form (e i k) (e j l)=0 := by
    rw [sub_mul, one_mul, hinv, sub_self]
  exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)

/-! ### Semidefinite forms and the radical -/

/-- A real affine function of `t` that is nonnegative everywhere has zero slope. -/
private theorem slope_eq_zero_of_nonneg {c d : ℝ} (h : ∀ t : ℝ, 0≤2*t*c+d) : c=0 := by
  by_contra hc
  have h1 := h (-(|d|+1)/(2*c))
  have h2 : 2*(-(|d|+1)/(2*c))*c=-(|d|+1) := by field_simp
  rw [h2] at h1
  have := le_abs_self d
  linarith

/-- **Cauchy–Schwarz kernel.**  For a positive semidefinite Hermitian form, an isotropic vector is
in the radical. -/
theorem form_eq_zero_of_isotropic (H : InvariantForm ρ m) (hpsd : ∀ x, 0≤(H.form x x).re)
    {u : ZeroAlgebra m} (hu : H.form u u=0) (v : ZeroAlgebra m) : H.form u v=0 := by
  have hexp : ∀ c : ℂ, (H.form (c • u+v) (c • u+v)).re=
      2*(conj c*H.form u v).re+(H.form v v).re := by
    intro c
    rw [form_add_left, form_add_right, form_add_right, form_smul_left, form_smul_left,
      form_smul_right, form_smul_right, hu, ← H.hermitian u v]
    have hc : (c*conj (H.form u v)).re=(conj c*H.form u v).re := by
      rw [← Complex.conj_re, map_mul, Complex.conj_conj]
    simp only [mul_zero, zero_add, Complex.add_re]
    rw [hc]
    ring
  have hre : (H.form u v).re=0 := by
    apply slope_eq_zero_of_nonneg (d := (H.form v v).re)
    intro t
    have := hpsd ((t:ℂ) • u+v)
    rw [hexp] at this
    have h2 : (conj (t:ℂ)*H.form u v).re=t*(H.form u v).re := by
      simp [Complex.mul_re]
    rw [h2] at this
    linarith
  have him : (H.form u v).im=0 := by
    apply slope_eq_zero_of_nonneg (d := (H.form v v).re)
    intro t
    have := hpsd (((t:ℂ)*I) • u+v)
    rw [hexp] at this
    have h2 : (conj ((t:ℂ)*I)*H.form u v).re=t*(H.form u v).im := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [h2] at this
    linarith
  exact Complex.ext hre him

/-- **The higher jets are radical.**  At a real point, a positive semidefinite invariant form
vanishes on every jet of order at least one. -/
theorem invariantForm_higherJet_radical (H : InvariantForm ρ m) (hpsd : ∀ x, 0≤(H.form x x).re)
    {i : ι} (hreal : (ρ i).im=0) (k : Fin (m i)) (hk : 1≤(k:ℕ)) (v : ZeroAlgebra m) :
    H.form (e i k) v=0 := by
  apply form_eq_zero_of_isotropic H hpsd _ v
  suffices hsuff : ∀ d : ℕ, ∀ k : Fin (m i), 1≤(k:ℕ) → m i-(k:ℕ)=d →
      H.form (e i k) (e i k)=0 from hsuff _ k hk rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro k hk hd
  have hrad : ∀ l : Fin (m i), (k:ℕ)<l → ∀ y, H.form (e i l) y=0 := by
    intro l hl y
    apply form_eq_zero_of_isotropic H hpsd _ y
    exact ih _ (by have := l.isLt; omega) l (by omega) rfl
  have hrad' : ∀ l : Fin (m i), (k:ℕ)<l → ∀ y, H.form y (e i l)=0 := by
    intro l hl y
    rw [← H.hermitian, hrad l hl y, map_zero]
  let k0 : Fin (m i) := ⟨(k:ℕ)-1, by omega⟩
  have hk0v : (k0:ℕ)=(k:ℕ)-1 := rfl
  have hne : k0≠k := fun h => by have := congrArg Fin.val h; omega
  have hle : k0≤k := by rw [Fin.le_def]; omega
  have hquad : ∀ q : ℚ, 0<q → (I*(Real.log q:ℂ))*H.form (e i k0) (e i k)+
      conj (I*(Real.log q:ℂ))*H.form (e i k) (e i k0)+
      conj (I*(Real.log q:ℂ))*(I*(Real.log q:ℂ))*H.form (e i k) (e i k)=0 := by
    intro q hq
    set a := Real.log q with ha
    have hinv := H.invariant q hq (e i k0) (e i k0)
    rw [form_act_e] at hinv
    let g : Fin (m i) → Fin (m i) → ℂ := fun k' l' => if k0≤k' ∧ k0≤l' then
      conj (jetCoeff (ρ i) a ((k':ℕ)-(k0:ℕ)))*jetCoeff (ρ i) a ((l':ℕ)-(k0:ℕ))*
        H.form (e i k') (e i l') else 0
    change (∑ k' : Fin (m i), ∑ l' : Fin (m i), g k' l')=_ at hinv
    have hA : ∀ k' : Fin (m i), k' ∉ ({k0, k} : Finset (Fin (m i))) → ∀ l', g k' l'=0 := by
      intro k' hk' l'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
      show (if k0≤k' ∧ k0≤l' then _ else _)=0
      split_ifs with h1
      · have h1' : (k0:ℕ)≤k' := h1.1
        have : (k':ℕ)≠k0 := fun h => hk'.1 (Fin.ext h)
        have : (k':ℕ)≠k := fun h => hk'.2 (Fin.ext h)
        rw [hrad k' (by omega), mul_zero]
      · rfl
    have hB : ∀ k' l' : Fin (m i), l' ∉ ({k0, k} : Finset (Fin (m i))) → g k' l'=0 := by
      intro k' l' hl'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl'
      show (if k0≤k' ∧ k0≤l' then _ else _)=0
      split_ifs with h1
      · have h1' : (k0:ℕ)≤l' := h1.2
        have : (l':ℕ)≠k0 := fun h => hl'.1 (Fin.ext h)
        have : (l':ℕ)≠k := fun h => hl'.2 (Fin.ext h)
        rw [hrad' l' (by omega), mul_zero]
      · rfl
    have hsum : (∑ k' : Fin (m i), ∑ l' : Fin (m i), g k' l')=
        (g k0 k0+g k0 k)+(g k k0+g k k) := by
      rw [← Finset.sum_subset (Finset.subset_univ ({k0, k} : Finset (Fin (m i))))
        (fun k' _ hk' => Finset.sum_eq_zero fun l' _ => hA k' hk' l'), Finset.sum_pair hne,
        ← Finset.sum_subset (Finset.subset_univ ({k0, k} : Finset (Fin (m i))))
          (fun l' _ hl' => hB k0 l' hl'), Finset.sum_pair hne,
        ← Finset.sum_subset (Finset.subset_univ ({k0, k} : Finset (Fin (m i))))
          (fun l' _ hl' => hB k l' hl'), Finset.sum_pair hne]
    have hu := conj_exp_mul_exp_self_of_real hreal a
    have h1 : (k:ℕ)-(k0:ℕ)=1 := by omega
    have g00 : g k0 k0=H.form (e i k0) (e i k0) := by
      show (if k0≤k0 ∧ k0≤k0 then _ else _)=_
      rw [if_pos ⟨le_rfl, le_rfl⟩, Nat.sub_self, jetCoeff_zero, hu, one_mul]
    have g01 : g k0 k=(I*(a:ℂ))*H.form (e i k0) (e i k) := by
      show (if k0≤k0 ∧ k0≤k then _ else _)=_
      rw [if_pos ⟨le_rfl, hle⟩, Nat.sub_self, h1, jetCoeff_zero, jetCoeff_one]
      linear_combination (I*(a:ℂ)*H.form (e i k0) (e i k))*hu
    have g10 : g k k0=conj (I*(a:ℂ))*H.form (e i k) (e i k0) := by
      show (if k0≤k ∧ k0≤k0 then _ else _)=_
      rw [if_pos ⟨hle, le_rfl⟩, Nat.sub_self, h1, jetCoeff_zero, jetCoeff_one, map_mul]
      linear_combination (conj (I*(a:ℂ))*H.form (e i k) (e i k0))*hu
    have g11 : g k k=conj (I*(a:ℂ))*(I*(a:ℂ))*H.form (e i k) (e i k) := by
      show (if k0≤k ∧ k0≤k then _ else _)=_
      rw [if_pos ⟨hle, hle⟩, h1, jetCoeff_one, map_mul]
      linear_combination (conj (I*(a:ℂ))*(I*(a:ℂ))*H.form (e i k) (e i k))*hu
    rw [hsum, g00, g01, g10, g11] at hinv
    linear_combination hinv
  have h2 := hquad 2 (by norm_num)
  have h4 := hquad 4 (by norm_num)
  have hlog4 : Real.log ((4:ℚ):ℝ)=2*Real.log ((2:ℚ):ℝ) := by
    rw [show ((4:ℚ):ℝ)=((2:ℚ):ℝ)^2 by norm_num, Real.log_pow]; norm_num
  rw [hlog4] at h4
  set L := Real.log ((2:ℚ):ℝ) with hL
  have hL0 : L≠0 := by rw [hL]; exact (Real.log_pos (by norm_num)).ne'
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal] at h2 h4
  push_cast at h4
  have hI : I^2=(-1:ℂ) := Complex.I_sq
  have hd : (L:ℂ)^2*H.form (e i k) (e i k)=0 := by
    linear_combination (h4-2*h2)/2+(L:ℂ)^2*H.form (e i k) (e i k)*hI
  exact (mul_eq_zero.mp hd).resolve_left (pow_ne_zero 2 (by exact_mod_cast hL0))

/-! ### Positive-definite invariant forms -/

/-- A positive-definite invariant form forces every point to be real and every multiplicity to be
one. -/
theorem posDef_invariantForm_real_simple (H : InvariantForm ρ m)
    (hpos : ∀ x : ZeroAlgebra m, x≠0 → 0<(H.form x x).re) (i : ι) (hm : 1 ≤ m i) :
    (ρ i).im=0 ∧ m i=1 := by
  have he : ∀ k : Fin (m i), e i k≠0 := fun k h => by
    have := congrArg (fun f : ZeroAlgebra m => f ⟨i, k⟩) h
    simp [e] at this
  let top : Fin (m i) := ⟨m i-1, by omega⟩
  have htop : (top:ℕ)+1=m i := by simp [top]; omega
  have hreal : (ρ i).im=0 := by
    have hinv := H.invariant 2 (by norm_num) (e i top) (e i top)
    rw [act_e_top _ i top htop, form_smul_left, form_smul_right, ← mul_assoc,
      conj_exp_mul_exp] at hinv
    have hv := hpos _ (he top)
    have hne : H.form (e i top) (e i top)≠0 := fun h0 => by rw [h0] at hv; simp at hv
    have hone := mul_right_cancel₀ hne (hinv.trans (one_mul _).symm)
    have hnorm := congrArg (‖·‖) hone
    simp only [norm_one, Complex.norm_exp] at hnorm
    rw [Real.exp_eq_one_iff] at hnorm
    have hre : (I*((Real.log ((2:ℚ):ℝ) : ℝ) : ℂ)*(ρ i-conj (ρ i))).re=
        -(2*Real.log ((2:ℚ):ℝ)*(ρ i).im) := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [hre] at hnorm
    have hl2 : (0:ℝ)<Real.log ((2:ℚ):ℝ) := Real.log_pos (by norm_num)
    have : Real.log ((2:ℚ):ℝ)*(ρ i).im=0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hl2.ne'
  refine ⟨hreal, ?_⟩
  by_contra hm1
  have hpsd : ∀ x, 0≤(H.form x x).re := by
    intro x
    by_cases hx : x=0
    · rw [hx, form_zero_left]; simp
    · exact (hpos x hx).le
  have hz := invariantForm_higherJet_radical H hpsd hreal top (by simp [top]; omega) (e i top)
  have hv := hpos _ (he top)
  rw [hz] at hv
  simp at hv

/-! ### The value pairing -/

/-- The pairing `Σ_ρ conj F(ρ) G(ρ)` of jet values. -/
def valuePairing : ZeroAlgebra m →ₗ⋆[ℂ] ZeroAlgebra m →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun x y => x.sum fun p c => if (p.2:ℕ)=0 then conj c*y p else 0)
    (fun x x' y => by
      rw [Finsupp.sum_add_index' (fun _ => by simp) (fun p c c' => by
        split_ifs <;> simp [add_mul])])
    (fun c x y => by
      rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.smul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      dsimp only
      split_ifs <;> simp [smul_eq_mul, mul_assoc])
    (fun x y y' => by
      rw [← Finsupp.sum_add]
      refine Finset.sum_congr rfl fun p _ => ?_
      dsimp only
      split_ifs <;> simp [mul_add])
    (fun c x y => by
      rw [RingHom.id_apply, Finsupp.smul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      dsimp only
      split_ifs <;> simp [smul_eq_mul]; ring)

theorem valuePairing_apply (x y : ZeroAlgebra m) :
    valuePairing x y=x.sum fun p c => if (p.2:ℕ)=0 then conj c*y p else 0 := rfl

theorem valuePairing_eq_sum (x y : ZeroAlgebra m) {s : Finset (JetIndex m)}
    (hs : x.support ⊆ s) :
    valuePairing x y=∑ p ∈ s, if (p.2:ℕ)=0 then conj (x p)*y p else 0 := by
  rw [valuePairing_apply, Finsupp.sum_of_support_subset x hs]
  intro p _
  split_ifs <;> simp

/-- On the value coordinates the action is the character. -/
theorem actBasis_apply_value [DecidableEq ι] (a : ℝ) (r p : JetIndex m) (hp : (p.2:ℕ)=0) :
    actBasis ρ m a r p=if r=p then Complex.exp (I*a*ρ p.1) else 0 := by
  unfold actBasis
  rw [Finsupp.finsetSum_apply]
  by_cases hrp : r=p
  · subst hrp
    rw [if_pos rfl, Finset.sum_eq_single r.2]
    · rw [if_pos le_rfl, Nat.sub_self, jetCoeff_zero, Finsupp.smul_apply, e,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
    · intro l _ hl
      split_ifs with h
      · rw [Finsupp.smul_apply, e, Finsupp.single_apply, if_neg, smul_zero]
        intro heq
        exact hl (Fin.ext (congrArg (fun s : JetIndex m => (s.2:ℕ)) heq))
      · rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hrp]
    apply Finset.sum_eq_zero
    intro l _
    split_ifs with h
    · rw [Finsupp.smul_apply, e, Finsupp.single_apply, if_neg, smul_zero]
      intro heq
      apply hrp
      have h2 : (l:ℕ)=(p.2:ℕ) := congrArg (fun s : JetIndex m => (s.2:ℕ)) heq
      have hr2 : (r.2:ℕ)=0 := by have := Fin.le_def.mp h; omega
      have hrl : r=⟨r.1, l⟩ := Sigma.ext rfl (heq_of_eq (Fin.ext (show (r.2:ℕ)=(l:ℕ) by omega)))
      rw [hrl]
      exact heq
    · rfl

theorem act_apply_value [DecidableEq ι] (a : ℝ) (x : ZeroAlgebra m) (p : JetIndex m) (hp : (p.2:ℕ)=0) :
    act ρ m a x p=Complex.exp (I*a*ρ p.1)*x p := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single r c =>
    rw [act, Finsupp.linearCombination_single, Finsupp.smul_apply, actBasis_apply_value a r p hp,
      Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> ring

theorem valuePairing_hermitian [DecidableEq ι] (x y : ZeroAlgebra m) :
    conj (valuePairing x y)=valuePairing y x := by
  rw [valuePairing_eq_sum x y (Finset.subset_union_left (s₂ := y.support)),
    valuePairing_eq_sum y x (Finset.subset_union_right (s₁ := x.support)), map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs
  · rw [map_mul, Complex.conj_conj, mul_comm]
  · simp

theorem valuePairing_invariant [DecidableEq ι] (hreal : ∀ i, (ρ i).im=0) (a : ℝ) (x y : ZeroAlgebra m) :
    valuePairing (act ρ m a x) (act ρ m a y)=valuePairing x y := by
  rw [valuePairing_eq_sum _ _ (Finset.subset_union_left (s₂ := x.support)),
    valuePairing_eq_sum x y (Finset.subset_union_right (s₁ := (act ρ m a x).support))]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with hp
  · rw [act_apply_value a x p hp, act_apply_value a y p hp, map_mul]
    linear_combination (conj (x p)*y p)*conj_exp_mul_exp_self_of_real (hreal p.1) a
  · rfl

theorem valuePairing_nonneg (x : ZeroAlgebra m) : 0≤(valuePairing x x).re := by
  rw [valuePairing_apply, Finsupp.sum, Complex.re_sum]
  apply Finset.sum_nonneg
  intro p _
  split_ifs
  · rw [mul_comm, Complex.mul_conj]; simp [Complex.normSq_nonneg]
  · simp

/-- **The value form.**  If every point is real, the value pairing is a positive semidefinite
invariant form. -/
def valueForm [DecidableEq ι] (hreal : ∀ i, (ρ i).im=0) : InvariantForm ρ m where
  form := valuePairing
  hermitian := valuePairing_hermitian
  invariant := fun _ _ x y => valuePairing_invariant hreal _ x y

/-- **Existence.**  If every point is real and simple, the value pairing is a positive-definite
invariant form. -/
theorem exists_posDef_invariantForm (hreal : ∀ i, (ρ i).im=0) (hsimple : ∀ i, m i=1) :
    ∃ H : InvariantForm ρ m, ∀ x : ZeroAlgebra m, x≠0 → 0<(H.form x x).re := by
  classical
  refine ⟨valueForm hreal, fun x hx => ?_⟩
  change 0<(valuePairing x x).re
  rw [valuePairing_apply, Finsupp.sum, Complex.re_sum]
  obtain ⟨p, hp⟩ := Finsupp.support_nonempty_iff.mpr hx
  have hval : ∀ q : JetIndex m, (q.2:ℕ)=0 := fun q => by
    have h1 := hsimple q.1
    have := q.2.isLt
    omega
  refine Finset.sum_pos' (fun q _ => ?_) ⟨p, hp, ?_⟩
  · rw [if_pos (hval q), mul_comm, Complex.mul_conj]; simp [Complex.normSq_nonneg]
  · rw [if_pos (hval p), mul_comm, Complex.mul_conj]
    have : x p≠0 := Finsupp.mem_support_iff.mp hp
    simpa [Complex.normSq_pos] using this

/-! ### The zero algebra of `Ξ` -/

/-- The zeros of `Ξ`. -/
abbrev XiZero := {z : ℂ // XiC z=0}

/-- The multiplicity of a zero of `Ξ`. -/
def xiMult (z : XiZero) : ℕ := analyticOrderNatAt XiC z.1

theorem XiC_analyticAt (z : ℂ) : AnalyticAt ℂ XiC z := XiC_differentiable.analyticAt z

theorem XiC_analyticOrderAt_ne_top (z : ℂ) : analyticOrderAt XiC z≠⊤ := by
  have hI : XiC (I/2)≠0 := by
    have h : (1/2 : ℂ)+I/2*I=0 := by ring_nf; rw [Complex.I_sq]; ring
    rw [XiC, h, xi]
    norm_num
  have h0 : analyticOrderAt XiC (I/2)≠⊤ := by
    rw [(XiC_analyticAt _).analyticOrderAt_eq_zero.mpr hI]
    exact ENat.zero_ne_top
  have hA : AnalyticOnNhd ℂ XiC Set.univ := fun z _ => XiC_analyticAt z
  exact hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ _)
    (Set.mem_univ _) h0

theorem one_le_xiMult (z : XiZero) : 1≤xiMult z := by
  by_contra h
  have h0 : analyticOrderNatAt XiC z.1=0 := by unfold xiMult at h; omega
  have hz : analyticOrderAt XiC z.1=0 := by
    rw [← Nat.cast_analyticOrderNatAt (XiC_analyticOrderAt_ne_top _), h0]
    rfl
  exact ((XiC_analyticAt _).analyticOrderAt_eq_zero.mp hz) z.2

/-- **The zero algebra of `Ξ` carries a positive-definite invariant Hermitian form iff RH holds and
every zero of `Ξ` is simple.** -/
theorem exists_posDef_invariantForm_XiC_iff :
    (∃ H : InvariantForm (fun z : XiZero => z.1) xiMult,
        ∀ x : ZeroAlgebra xiMult, x≠0 → 0<(H.form x x).re) ↔
      RiemannHypothesis ∧ ∀ z : ℂ, XiC z=0 → analyticOrderNatAt XiC z=1 := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · rintro ⟨H, hpos⟩
    exact ⟨fun z hz => (posDef_invariantForm_real_simple H hpos ⟨z, hz⟩ (one_le_xiMult _)).1,
      fun z hz => (posDef_invariantForm_real_simple H hpos ⟨z, hz⟩ (one_le_xiMult _)).2⟩
  · rintro ⟨hreal, hsimple⟩
    exact exists_posDef_invariantForm (fun z => hreal z.1 z.2) (fun z => hsimple z.1 z.2)

end

end RHTower.ZeroAlgebraInvariantForms
