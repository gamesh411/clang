int callback_to_main(int x);
int f(int x) {
  return x - 1;
}

int g(int x) {
  return callback_to_main(x) + 1;
}

int h_chain(int);

int h(int x) {
  return 2 * h_chain(x);
}

namespace myns {
int fns(int x) {
  return x + 7;
}

namespace embed_ns {
int fens(int x) {
  return x - 3;
}
}

class embed_cls {
public:
  int fecl(int x) {
    return x - 7;
  }
};
}

class mycls {
public:
  int fcl(int x) {
    return x + 5;
  }
  static int fscl(int x) {
    return x + 6;
  }

  class embed_cls2 {
  public:
    int fecl2(int x) {
      return x - 11;
    }
  };
};

namespace chns {
int chf2(int x);

class chcls {
public:
  int chf4(int x);
};

int chf3(int x) {
  return chcls().chf4(x);
}

int chf1(int x) {
  return chf2(x);
}
}

// Test for a crash when importing typedefs.
struct AVBuffer {
	int a;
};

typedef struct AVBuffer avt;
int avtSize(void){
	return sizeof(avt);
}
