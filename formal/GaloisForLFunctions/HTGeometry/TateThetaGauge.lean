import GaloisForLFunctions.HTGeometry.MultiplicativeTheta

/-!
# Tate theta gauge at a quarter nome
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive fourth root `r`; the elliptic nome is `q=r^4`. -/
structure TateQuarterNome where
  root : ℝ
  root_pos : 0 < root
  root_lt_one : root < 1

namespace TateQuarterNome

/-- The actual elliptic nome `q=r^4`. -/
def nome (r : TateQuarterNome) : EulerNome where
  val := (r.root : ℂ) ^ 4
  norm_lt_one := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos r.root_pos]
    exact pow_lt_one₀ r.root_pos.le r.root_lt_one (by norm_num)

@[simp]
theorem coe_nome (r : TateQuarterNome) :
    ((r.nome : EulerNome) : ℂ) = (r.root : ℂ) ^ 4 := rfl

theorem root_complex_ne_zero (r : TateQuarterNome) : (r.root : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr r.root_pos.ne'

theorem nome_ne_zero (r : TateQuarterNome) : ((r.nome : EulerNome) : ℂ) ≠ 0 :=
  pow_ne_zero 4 r.root_complex_ne_zero

end TateQuarterNome

/-- Zero orbit `[r]` on `ℂˣ/q^ℤ`, written in the fourth-root coordinate. -/
def tateThetaZeroOrbit (r : TateQuarterNome) (x : ℂ) : Prop :=
  ∃ k : ℤ, x = (r.root : ℂ) ^ (4 * k + 1)

/-- Pole orbit `[r^3]` on `ℂˣ/q^ℤ`, written in the fourth-root coordinate. -/
def tateThetaPoleOrbit (r : TateQuarterNome) (x : ℂ) : Prop :=
  ∃ k : ℤ, x = (r.root : ℂ) ^ (4 * k + 3)

/-- A shifted theta factor has the exact translated nome orbit as its zero set. -/
theorem multiplicativeTheta_rootShift_eq_zero_iff
    (r : TateQuarterNome) (a : ℤ) (x : ℂ) :
    multiplicativeTheta r.nome ((r.root : ℂ) ^ a * x) = 0 ↔
      ∃ k : ℤ, x = (r.root : ℂ) ^ (4 * k - a) := by
  rw [multiplicativeTheta_eq_zero_iff_nome_zpow r.nome r.nome_ne_zero]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ (zpow_ne_zero a r.root_complex_ne_zero)
    rw [hk, ← zpow_add₀ r.root_complex_ne_zero]
    rw [show ((r.nome : EulerNome) : ℂ) ^ k =
        (r.root : ℂ) ^ (4 * k) by
      rw [TateQuarterNome.coe_nome, ← zpow_natCast, ← zpow_mul]
      norm_num]
    congr 1
    ring
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    rw [← zpow_add₀ r.root_complex_ne_zero]
    rw [TateQuarterNome.coe_nome, ← zpow_natCast, ← zpow_mul]
    norm_num

/-- Both numerator theta factors vanish on the same orbit `[r]`. -/
theorem tateThetaNumerator_eq_zero_iff (r : TateQuarterNome) (x : ℂ) :
    multiplicativeTheta r.nome ((r.root : ℂ) ^ (-1 : ℤ) * x) *
        multiplicativeTheta r.nome ((r.root : ℂ) ^ (3 : ℤ) * x) = 0 ↔
      tateThetaZeroOrbit r x := by
  rw [mul_eq_zero, multiplicativeTheta_rootShift_eq_zero_iff,
    multiplicativeTheta_rootShift_eq_zero_iff]
  constructor
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · exact ⟨k, by convert hk using 1 <;> ring⟩
    · exact ⟨k - 1, by convert hk using 1 <;> ring⟩
  · rintro ⟨k, hk⟩
    exact Or.inl ⟨k, by convert hk using 1 <;> ring⟩

/-- Denominator theta factor vanishes exactly on the orbit `[r^3]`. -/
theorem tateThetaDenominator_eq_zero_iff (r : TateQuarterNome) (x : ℂ) :
    multiplicativeTheta r.nome ((r.root : ℂ) ^ (1 : ℤ) * x) = 0 ↔
      tateThetaPoleOrbit r x := by
  rw [multiplicativeTheta_rootShift_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k - 1, by convert hk using 1 <;> ring⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by convert hk using 1 <;> ring⟩

/-- The zero and pole orbits are disjoint because `0<r<1`. -/
theorem tateThetaZeroOrbit_disjoint_poleOrbit (r : TateQuarterNome) (x : ℂ) :
    ¬ (tateThetaZeroOrbit r x ∧ tateThetaPoleOrbit r x) := by
  rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have heq : (r.root : ℂ) ^ (4 * k + 1) = (r.root : ℂ) ^ (4 * l + 3) :=
    hk.symm.trans hl
  have habs := congrArg norm heq
  simp only [norm_zpow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos r.root_pos] at habs
  have hinj : Function.Injective (fun n : ℤ => r.root ^ n) := by
    intro m n hmn
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (ne_of_lt (zpow_lt_zpow_right_of_lt_one₀
        r.root_pos r.root_lt_one hlt)) hmn.symm
    · exact (ne_of_lt (zpow_lt_zpow_right_of_lt_one₀
        r.root_pos r.root_lt_one hgt)) hmn
  have hexp : 4 * k + 1 = 4 * l + 3 := hinj habs
  omega

/-- Tate-theta meromorphic gauge from the card, in the coordinate `q=r^4`. -/
def tateThetaGauge (r : TateQuarterNome) (x : ℂ) : ℂ :=
  -(r.root : ℂ) *
    multiplicativeTheta r.nome ((r.root : ℂ) ^ (-1 : ℤ) * x) *
    multiplicativeTheta r.nome ((r.root : ℂ) ^ (3 : ℤ) * x) /
      multiplicativeTheta r.nome ((r.root : ℂ) ^ (1 : ℤ) * x) ^ 2

/-- Exact `q`-ellipticity: `E_q(qx)=E_q(x)`. -/
theorem tateThetaGauge_mul_nome (r : TateQuarterNome) (x : ℂ) (hx : x ≠ 0) :
    tateThetaGauge r (((r.nome : EulerNome) : ℂ) * x) = tateThetaGauge r x := by
  let u : ℂ := (r.root : ℂ) ^ (-1 : ℤ) * x
  let v : ℂ := (r.root : ℂ) ^ (3 : ℤ) * x
  let w : ℂ := (r.root : ℂ) ^ (1 : ℤ) * x
  have hu : u ≠ 0 := mul_ne_zero (zpow_ne_zero _ r.root_complex_ne_zero) hx
  have hv : v ≠ 0 := mul_ne_zero (zpow_ne_zero _ r.root_complex_ne_zero) hx
  have hw : w ≠ 0 := mul_ne_zero (zpow_ne_zero _ r.root_complex_ne_zero) hx
  have huShift : (r.root : ℂ) ^ (-1 : ℤ) * (((r.nome : EulerNome) : ℂ) * x) =
      ((r.nome : EulerNome) : ℂ) * u := by
    simp only [u, TateQuarterNome.coe_nome]
    ring
  have hvShift : (r.root : ℂ) ^ (3 : ℤ) * (((r.nome : EulerNome) : ℂ) * x) =
      ((r.nome : EulerNome) : ℂ) * v := by
    simp only [v, TateQuarterNome.coe_nome]
    ring
  have hwShift : (r.root : ℂ) ^ (1 : ℤ) * (((r.nome : EulerNome) : ℂ) * x) =
      ((r.nome : EulerNome) : ℂ) * w := by
    simp only [w, TateQuarterNome.coe_nome]
    ring
  have huv : u * v = w ^ 2 := by
    simp only [u, v, w]
    field_simp [r.root_complex_ne_zero]
  rw [tateThetaGauge, tateThetaGauge, huShift, hvShift, hwShift,
    multiplicativeTheta_mul_nome r.nome r.nome_ne_zero u hu,
    multiplicativeTheta_mul_nome r.nome r.nome_ne_zero v hv,
    multiplicativeTheta_mul_nome r.nome r.nome_ne_zero w hw]
  have hmult : (-u⁻¹) * (-v⁻¹) = (-w⁻¹) ^ 2 := by
    field_simp [hu, hv, hw]
    exact huv.symm
  change -(r.root : ℂ) * (-u⁻¹ * multiplicativeTheta r.nome u) *
      (-v⁻¹ * multiplicativeTheta r.nome v) /
        (-w⁻¹ * multiplicativeTheta r.nome w) ^ 2 =
    -(r.root : ℂ) * multiplicativeTheta r.nome u *
      multiplicativeTheta r.nome v / multiplicativeTheta r.nome w ^ 2
  rw [mul_pow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  field_simp [hu, hv, hw] at hmult
  rw [show ((-w⁻¹) ^ 2)⁻¹ = u * v by
    field_simp [hu, hv, hw]
    exact huv.symm]
  ring_nf
  simp [hu, hv]

end

end GaloisForLFunctions.HTGeometry
