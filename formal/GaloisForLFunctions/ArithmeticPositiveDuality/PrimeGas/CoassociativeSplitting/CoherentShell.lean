import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting.Classification

/-! # A coassociative isometry with a coherently split composite shell -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting

private def ordinary (n : ℕ+) : ℕ+ × ℕ+ :=
  if n=3 ∨ n=6 then (1,n) else (n,1)

private theorem ordinary_product (n : ℕ+) : (ordinary n).1*(ordinary n).2=n := by
  unfold ordinary
  split_ifs <;> simp

/-- The two ways to split 12 share the same triple-output bracketing.
Shells 3 and 6 face right, and the remaining simple branches face left. -/
def coherent (u v : ℂ) (a b : ℕ+) : ℂ :=
  if a*b=12 then if (a,b)=(2,6) then u else if (a,b)=(4,3) then v else 0
  else if (a,b)=ordinary (a*b) then 1 else 0

private theorem other_norm (u v : ℂ) {n : ℕ+} (hn : n≠12) :
    HasSum (shell (coherent u v) n) 1 := by
  refine (hasSum_ite_eq (ordinary n) (1:ℝ)).congr_fun fun x => ?_
  by_cases prod : x.1*x.2=n
  · rw [shell,if_pos prod,coherent,prod,if_neg hn]
    by_cases eqn : x=ordinary n <;> simp [eqn]
  · have ne : x≠ordinary n := fun e => prod (e ▸ ordinary_product n)
    rw [shell,if_neg prod,if_neg ne]

private theorem first_product : (2:ℕ+)*6=12 := rfl
private theorem second_product : (4:ℕ+)*3=12 := rfl

private theorem twelve_norm (u v : ℂ) : HasSum (shell (coherent u v) 12) (‖u‖^2+‖v‖^2) := by
  refine ((hasSum_ite_eq ((2,6):ℕ+ × ℕ+) (‖u‖^2)).add
    (hasSum_ite_eq ((4,3):ℕ+ × ℕ+) (‖v‖^2))).congr_fun fun x => ?_
  by_cases first : x=(2,6)
  · subst x
    norm_num [shell,coherent,first_product]
  by_cases second : x=(4,3)
  · subst x
    norm_num [shell,coherent,second_product]
  · by_cases prod : x.1*x.2=12 <;> simp [shell,coherent,prod,first,second]

private theorem coherent_endpoints (u v : ℂ) : endpoints (coherent u v) := by
  have unit : coherent u v 1 1=1 := by norm_num [coherent,ordinary]
  intro a b nz
  rw [unit]
  by_cases twelve : a*b=12
  · by_cases p : (a,b)=(2,6)
    · have ha : a=2 := congrArg Prod.fst p
      have hb : b=6 := congrArg Prod.snd p
      rw [ha,hb]
      norm_num [coherent,ordinary]
    by_cases q : (a,b)=(4,3)
    · have ha : a=4 := congrArg Prod.fst q
      have hb : b=3 := congrArg Prod.snd q
      rw [ha,hb]
      norm_num [coherent,ordinary]
    · exact False.elim (nz (by simp only [coherent,if_pos twelve,if_neg p,if_neg q]))
  · have eqn : (a,b)=ordinary (a*b) := by
      by_contra ne
      exact nz (by simp only [coherent,if_neg twelve,if_neg ne])
    by_cases right : a*b=3 ∨ a*b=6
    · rw [ordinary,if_pos right] at eqn
      have ae : a=1 := congrArg Prod.fst eqn
      subst a
      rw [one_mul] at right twelve
      exact ⟨unit,by simp [coherent,ordinary,right,twelve]⟩
    · rw [ordinary,if_neg right] at eqn
      have be : b=1 := congrArg Prod.snd eqn
      subst b
      rw [mul_one] at right twelve
      exact ⟨by simp [coherent,ordinary,right,twelve],unit⟩

/-- An arbitrary normalized complex pair is realized on the actual integer
shell 12, with no other constraint on its relative phase or its two masses. -/
theorem coherent_iff (u v : ℂ) : isometric (coherent u v) ∧ coassociative (coherent u v) ↔
    ‖u‖^2+‖v‖^2=1 := by
  rw [classification]
  constructor
  · intro h
    exact (twelve_norm u v).unique (h.1 12)
  · intro unit
    refine ⟨fun n => ?_,coherent_endpoints u v⟩
    by_cases twelve : n=12
    · rw [twelve,←unit]
      exact twelve_norm u v
    · exact other_norm u v twelve

theorem coherent_pair (u v : ℂ) : coherent u v 2 6=u ∧ coherent u v 4 3=v := by
  norm_num [coherent,first_product,second_product]

#print axioms coherent_iff
#print axioms coherent_pair

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting
