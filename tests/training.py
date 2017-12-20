from learn.dsloader import *
from learn.embedding import sentence_len, word_size

from keras.models import Sequential
from keras.layers import Dense, Activation, LSTM, Dropout

_epochs = 20
_num_train = None
_num_test = None
_batch_size = 50

_num_lstm_layers = 4
_num_hidden = 1024

mode = 'reoonly'

if mode == 'reoonly':
    train_set_X, train_set_Y = load_dataset('reo_ds.txt', _num_train)
    test_set_X = train_set_X[-20:]
    test_set_Y = train_set_Y[-20:]
    train_set_X = train_set_X[:-20]
    train_set_Y = train_set_Y[:-20]

    _num_hidden = 1024
    _num_lstm_layers = 3

    _batch_size = 20
    _epochs = 60
elif mode == 'coqonly':
    _num_train = 2000

    train_set_X, train_set_Y = load_dataset('raw_ds.txt', _num_train)
    test_set_X = train_set_X[-500:]
    test_set_Y = train_set_Y[-500:]
    train_set_X = train_set_X[:-500]
    train_set_Y = train_set_Y[:-500]

    _batch_size = 50
    _epochs = 15
else:
    train_set_X, train_set_Y = load_dataset('raw_ds.txt', _num_train)
    test_set_X, test_set_Y = load_dataset('reo_ds.txt', _num_test)

print("data analyzing done.")

lstm_word_width = sentence_len * word_size
lstm_time_step = time_step
lstmlayers = 4

model = Sequential()
for _ in range(1, _num_lstm_layers):
    model.add(LSTM(_num_hidden, input_shape=(lstm_time_step, lstm_word_width), activation='sigmoid', return_sequences=True))
    model.add(Dropout(0.2))

model.add(LSTM(_num_hidden, input_shape=(lstm_time_step, lstm_word_width), activation='sigmoid'))
model.add(Dropout(0.2))

model.add(Dense(len(supported_tactics)))
model.add(Activation('softmax'))
model.compile(loss='categorical_crossentropy', optimizer='rmsprop')

print(model.input_shape)
print("keras model built. start training")
model.fit(train_set_X, train_set_Y, batch_size=_batch_size, epochs=_epochs)

test_result = model.predict(test_set_X)
target_result = [list(line).index(max(line)) for line in test_set_Y]

for i in range(1, 11):
    # verify
    test_result_n = [get_maximum_indexes(line, i) for line in test_result]
    target_result = [list(line).index(max(line)) for line in test_set_Y]

    correctness = float(sum([1 if target_result[j] in test_result_n[j] else 0 for j in range(len(target_result))])) / len(target_result)
    print("CORRECTNESS when selecting %d tactics: %f percents" % (i, correctness))