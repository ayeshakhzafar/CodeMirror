# 🧠 CodeMirror – Web-Based Program Verification Tool

**CodeMirror** is a web-based application that helps analyze the **correctness** and **semantic equivalence** of programs written in a **custom mini-language**. Built using **React**, the tool leverages **formal methods** by converting code into **Static Single Assignment (SSA)** form and generating **SMT-LIB constraints** to verify them using the **Z3 SMT solver**.

---

## 🚀 Features

- ✅ **Mini-language Parser** (PEG.js-based):
  - Variable assignments using `:=` or `=`
  - Control structures: `if`, `while`, `for`
  - Arrays and array indexing
  - Quantified assertions (e.g., `forall`, `exists`)

- 🧠 **SSA Transformation**:
  - Variable versioning
  - Phi node generation for branching
  - Expression rewriting and concrete value tracking

- 🔁 **Loop Unrolling**:
  - Configurable depth
  - Static termination detection
  - Transforms loops into nested `if` blocks

- 🧩 **SMT-LIB2 Constraint Generator**:
  - QF_ALIA logic (Quantifier-Free Arrays and Linear Integer Arithmetic)
  - Full SSA-to-SMT conversion
  - Assertion and equivalence verification

- 📈 **Graph Visualization** (React Flow):
  - Control flow graph (CFG)
  - SSA control flow graph
  - Data flow graph for variable dependencies

- 🔍 **Verification Modes**:
  - Program correctness (via `assert`)
  - Semantic equivalence of two programs

- 🔗 **Z3 Solver Integration**:
  - Runs Z3 locally in WebAssembly (in-browser)
  - Option to export SMT to [FM Playground Z3](https://fmplayground.com/z3)

---

## 📦 Technologies Used

- **React** (UI framework)
- **PEG.js** (parser generator for mini-language)
- **Tailwind CSS** (UI styling)
- **Z3 SMT Solver** (WebAssembly & external link)
- **React Flow** (graph rendering)
- **JavaScript** (SSA & SMT logic)

---

## 📄 Sample Programs to Try

Below are some example programs you can run in the tool. You can paste them directly into the editor.

### FOR VERIFICATION:

#### For loop:

for (i := 0; i < n; i := i + 1) { for (j := 0; j < n - i - 1; j := j + 1) { if (arr[j] > arr[j+1]) { temp := arr[j]; arr[j] := arr[j+1]; arr[j+1] := temp; } } } assert(for (i in range (n)):arr[i] < arr[i+1]);

#### Insertion sort:

for (i := 1; i < n; i := i + 1) {
  key := arr[i];
  j := i - 1;
  while (j >= 0 && arr[j] > key) {
    arr[j + 1] := arr[j];
    j := j - 1;
  }
  arr[j + 1] := key;
}
assert(for (i in range (n-1)): arr[i] <= arr[i+1]);

#### Bubble sort:

for (i := 0; i < n; i := i + 1) {
  for (j := 0; j < n - i - 1; j := j + 1) {
    if (arr[j] > arr[j+1]) {
      temp := arr[j];
      arr[j] := arr[j+1];
      arr[j+1] := temp;
    }
  }
}
assert(for (i in range (n-1)):arr[i] < arr[i+1]);

#### while loop:
x := 0;
while (x < 4) {
  x := x + 1;
}
assert(x == 4);

#### If else:
x := 3;
if (x < 5) {
  y := x + 1;
} else {
  y := x - 1;
}
assert(y > 0);


### FOR EQUIVALENCE:

#### 1st pair:

x := 0;
while (x < 4) {
  x := x + 1;
}
assert(x == 4);

---
---

x := 0;
for (i := 0; i < 4; i := i + 1) {
  x := x + 1;
}
assert(x == 4);


#### 2nd pair:

n := 10;  
sum := 0;
i := 1;
while (i <= n) {
  sum := sum + i;
  i := i + 1;
}
assert(sum >= 0);  

---
---

n := 10;  
sum := 0;
if (n >= 0) {
  sum := n * (n + 1) / 2;
}
assert(sum >= 0); 

---

## 📌 Screenshots

### VERIFICATION MODE:
#### INSERTION SORT:

![image](https://github.com/user-attachments/assets/2c9f8f4c-edf2-41d3-8404-54bef3da9853)
![image](https://github.com/user-attachments/assets/d46b68f6-2202-46c4-a4bb-6712f4a61819)
![image](https://github.com/user-attachments/assets/67309029-715b-4857-91d2-fb057b7c0495)
![image](https://github.com/user-attachments/assets/29a87f90-680b-47bc-ab75-a0285475bf66)
![image](https://github.com/user-attachments/assets/62262934-dbdf-48bf-b05a-0410f0860078)
![image](https://github.com/user-attachments/assets/505823f3-6c00-4903-9134-ba4ac6d1583c)

#### IF ELSE:

![image](https://github.com/user-attachments/assets/10ff6781-90ae-42b5-9e28-4a50bfc3ca2e)
![image](https://github.com/user-attachments/assets/7bc242f3-7ebe-4d6e-a05b-961edd87051d)
![image](https://github.com/user-attachments/assets/e7b16f25-3f21-4074-bb4d-8c562aed3ead)
![image](https://github.com/user-attachments/assets/15b2bc6e-cd45-46d6-8b11-19b27f7cad79)
![image](https://github.com/user-attachments/assets/0a8b1b42-8497-40a8-976f-4a225554e337)
![image](https://github.com/user-attachments/assets/bbf892f0-a2f2-4087-ad21-08f15981b6c7)

### EQUIVALENCE MODE:

![image](https://github.com/user-attachments/assets/9bdaee30-df55-4799-a4d8-9b6795b21649)
![image](https://github.com/user-attachments/assets/0a90d994-20a0-4aea-bfb0-7829f33a3eae)
![image](https://github.com/user-attachments/assets/e23b6f3f-5140-4bc3-a57e-7d6b151af14f)
![image](https://github.com/user-attachments/assets/56f1b930-4dc3-4f8c-8b8f-2d0dabea8a94)

### LOOP UNROLLING MODE:

![image](https://github.com/user-attachments/assets/171430fa-dedb-4ab1-9ab6-40a289c8db5f)
![image](https://github.com/user-attachments/assets/36f0103e-3243-4564-b20c-c6b64f3171a1)

---

## ⚠️ Known Limitations

- ❌ Does not model **integer overflows** — assumes unbounded integers.
- 🧮 Limited support for **integers** and **integer arrays** only.
- ∀ ∃ Quantifier-heavy assertions may be **difficult for Z3** to handle efficiently.
- 🐢 Performance may degrade for **large or deeply nested programs** due to SSA and SMT complexity.

---

## ✨ Future Improvements

- 🧠 Add **symbolic execution** and **counterexample generation** for better analysis.
- 🧬 Support **functions**, **recursion**, and a **richer type system** (e.g., booleans, strings).
- 🧩 Implement **modular** and **parallel verification** techniques for better scalability.
- 📣 Improve **error reporting** and counterexample display for easier debugging.
- 🧑‍🏫 Integrate **interactive proof assistance** when automatic verification fails.

---
Made by Ayesha 🧪
