import PEqualNP.Defs
import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_3773

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def shift (n i : ℕ) := if i < n then i else i+1

def shiftedGate (n : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (shift n)⟩

def evalStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma readShift (x w : List Bool) (b : Bool) (i : ℕ) :
    ((x ++ [b]) ++ w).getD (shift x.length i) false = (x ++ w).getD i false := by
  by_cases h : i < x.length
  · rw [shift,ite_eq_left h]
    rw [List.getD_append _ _ _ _ (by simp; omega),List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ h]
  · rw [shift,ite_eq_right h]
    rw [List.getD_append_right _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by omega)]
    simp only [List.length_append,List.length_singleton]
    congr 1; omega

lemma runShift (gs : List Gate) (x : List Bool) (b : Bool) (w : List Bool) :
    ∃ t : List Bool, t.length = w.length + gs.length ∧
    gs.foldl evalStep (x ++ w) = x ++ t ∧
    (gs.map (shiftedGate x.length)).foldl evalStep ((x ++ [b]) ++ w) = (x ++ [b]) ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨w,by simp,rfl,rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => (x++w).getD i false)
    have he : evalStep ((x++[b])++w) (shiftedGate x.length g) = (x++[b])++(w++[v]) := by
      simp only [evalStep,shiftedGate,List.map_map,Function.comp_def,readShift,v]
      rw [List.append_assoc]
    have ho : evalStep (x++w) g = x++(w++[v]) := by simp [evalStep,v,List.append_assoc]
    obtain ⟨t,hlen,hor,hne⟩ := ih (w++[v])
    refine ⟨t,by simp at hlen ⊢; omega,?_,?_⟩
    · simpa only [List.foldl_cons,ho] using hor
    · simpa only [List.map_cons,List.foldl_cons,he] using hne

def firstFlag : Gate := ⟨.and,[0,13]⟩
def lastFlag (C : Circuit) : Gate := ⟨.or,[26,shift 26 C.output]⟩

def assemble (C : Circuit) : Circuit :=
  ⟨firstFlag :: (C.gates.map (shiftedGate 26) ++ [lastFlag C]), 27+C.gates.length⟩

lemma assembled_size (C : Circuit) : (assemble C).size = C.size+2 := by
  simp [Circuit.size,assemble,Nat.add_assoc]

lemma assembled_mono (C : Circuit) (h : Monotone2 C) : Monotone2 (assemble C) := by
  intro g hg
  change g ∈ firstFlag :: (C.gates.map (shiftedGate 26) ++ [lastFlag C]) at hg
  rcases List.mem_cons.mp hg with rfl | hg
  · simp [firstFlag]
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    simpa [shiftedGate] using h a ha
  · obtain rfl := List.mem_singleton.mp hg
    simp [lastFlag]

lemma getLast (xs : List Bool) (b : Bool) : (xs++[b]).getD xs.length false = b := by
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma assembled_eval (C : Circuit) (x : Fin 26 → Bool) :
    (assemble C).eval (List.ofFn x) = ((x 0 && x 13) || C.eval (List.ofFn x)) := by
  let xs := List.ofFn x
  let b := x 0 && x 13
  have hx : xs.length = 26 := by simp [xs]
  have ini : evalStep xs firstFlag = xs++[b] := by
    have rd (i : ℕ) (hi : i < 26) : xs.getD i false = x ⟨i,hi⟩ := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_ofFn ..
    change xs ++ [xs.getD 0 false && (xs.getD 13 false && true)] = xs++[b]
    rw [rd 0 (by decide),rd 13 (by decide),Bool.and_true]
    rfl
  obtain ⟨t,ht,ho,hn⟩ := runShift C.gates xs b []
  simp only [List.append_nil,List.length_nil,Nat.zero_add,hx] at ht ho hn
  have old : C.eval xs = (xs++t).getD C.output false := by
    change (C.gates.foldl evalStep xs).getD C.output false = _
    rw [ho]
  have firstRead : ((xs++[b])++t).getD 26 false = b := by
    rw [List.getD_append _ _ _ _ (by simp [hx])]
    rw [←hx,getLast]
  have secondRead : ((xs++[b])++t).getD (shift 26 C.output) false = C.eval xs := by
    rw [old,← hx,readShift]
  let V := (xs++[b])++t
  have last : evalStep V (lastFlag C) = V++[b || C.eval xs] := by
    change V ++ [V.getD 26 false || (V.getD (shift 26 C.output) false || false)] = _
    change V.getD 26 false = b at firstRead
    change V.getD (shift 26 C.output) false = C.eval xs at secondRead
    rw [firstRead,secondRead,Bool.or_false]
  change (((C.gates.map (shiftedGate 26) ++ [lastFlag C]).foldl evalStep (evalStep xs firstFlag)).getD
    (27+C.gates.length) false) = _
  rw [ini,List.foldl_append,hn]
  change (evalStep V (lastFlag C)).getD (27+C.gates.length) false = _
  rw [last]
  have hlen : 27+C.gates.length=V.length := by simp [V,hx,ht]; omega
  rw [hlen,getLast]

theorem compileFlag : ∀ D : Circuit, Monotone2 D → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 2 ∧
    (∃ g : Gate, C.gates.head? = some g ∧ g.op = GateOp.and ∧ g.inputs = [0,13]) ∧
    ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = ((x 0 && x 13) || D.eval (List.ofFn x)) := by
  intro D hm
  exact ⟨assemble D,assembled_mono D hm,(assembled_size D).le,⟨firstFlag,rfl,rfl,rfl⟩,assembled_eval D⟩

end PEqualNP.Outside.L_meta_3773
